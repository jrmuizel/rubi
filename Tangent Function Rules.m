(* ::Package:: *)

(* ::Section:: *)
(*Tangent Function Rules*)


(* ::Subsection::Closed:: *)
(*1 (c tan)^n*)


Int[tan[a_.+b_.*x_],x_Symbol] :=
  -Log[RemoveContent[Cos[a+b*x],x]]/b /;
FreeQ[{a,b},x]


Int[cot[a_.+b_.*x_],x_Symbol] :=
  Log[RemoveContent[Sin[a+b*x],x]]/b /;
FreeQ[{a,b},x]


Int[(c_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  c*(c*Tan[a+b*x])^(n-1)/(b*(n-1)) - 
  c^2*Int[(c*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*(c*Cot[a+b*x])^(n-1)/(b*(n-1)) - 
  c^2*Int[(c*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


(* Int[1/tan[a_.+b_.*x_],x_Symbol] :=
  Log[RemoveContent[Sin[a+b*x],x]]/b /;
FreeQ[{a,b},x] *)


(* Int[1/cot[a_.+b_.*x_],x_Symbol] :=
  -Log[RemoveContent[Cos[a+b*x],x]]/b /;
FreeQ[{a,b},x] *)


Int[(c_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Tan[a+b*x])^(n+1)/(b*c*(n+1)) - 
  1/c^2*Int[(c*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Cot[a+b*x])^(n+1)/(b*c*(n+1)) - 
  1/c^2*Int[(c*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[Sqrt[c_*tan[a_.+b_.*x_]],x_Symbol] :=
  c/(2*I)*Int[(1+I*Tan[a+b*x])/Sqrt[c*Tan[a+b*x]],x] - c/(2*I)*Int[(1-I*Tan[a+b*x])/Sqrt[c*Tan[a+b*x]],x] /;
FreeQ[{a,b,c},x] && MatchQ[c,d_.*Complex[m_,n_]]


Int[Sqrt[c_.*tan[a_.+b_.*x_]],x_Symbol] :=
  c/2*Int[(1+Tan[a+b*x])/Sqrt[c*Tan[a+b*x]],x] - c/2*Int[(1-Tan[a+b*x])/Sqrt[c*Tan[a+b*x]],x] /;
FreeQ[{a,b,c},x]


Int[Sqrt[c_*cot[a_.+b_.*x_]],x_Symbol] :=
  c/(2*I)*Int[(1+I*Cot[a+b*x])/Sqrt[c*Cot[a+b*x]],x] - c/(2*I)*Int[(1-I*Cot[a+b*x])/Sqrt[c*Cot[a+b*x]],x] /;
FreeQ[{a,b,c},x] && MatchQ[c,d_.*Complex[m_,n_]]


Int[Sqrt[c_.*cot[a_.+b_.*x_]],x_Symbol] :=
  c/2*Int[(1+Cot[a+b*x])/Sqrt[c*Cot[a+b*x]],x] - c/2*Int[(1-Cot[a+b*x])/Sqrt[c*Cot[a+b*x]],x] /;
FreeQ[{a,b,c},x]


Int[1/Sqrt[c_.*tan[a_.+b_.*x_]],x_Symbol] :=
  1/2*Int[(1+I*Tan[a+b*x])/Sqrt[c*Tan[a+b*x]],x] + 1/2*Int[(1-I*Tan[a+b*x])/Sqrt[c*Tan[a+b*x]],x] /;
FreeQ[{a,b,c},x] && MatchQ[c,d_.*Complex[m_,n_]]


Int[1/Sqrt[c_.*tan[a_.+b_.*x_]],x_Symbol] :=
  1/2*Int[(1+Tan[a+b*x])/Sqrt[c*Tan[a+b*x]],x] + 1/2*Int[(1-Tan[a+b*x])/Sqrt[c*Tan[a+b*x]],x] /;
FreeQ[{a,b,c},x]


Int[1/Sqrt[c_.*cot[a_.+b_.*x_]],x_Symbol] :=
  1/2*Int[(1+I*Cot[a+b*x])/Sqrt[c*Cot[a+b*x]],x] + 1/2*Int[(1-I*Cot[a+b*x])/Sqrt[c*Cot[a+b*x]],x] /;
FreeQ[{a,b,c},x] && MatchQ[c,d_.*Complex[m_,n_]]


Int[1/Sqrt[c_.*cot[a_.+b_.*x_]],x_Symbol] :=
  1/2*Int[(1+Cot[a+b*x])/Sqrt[c*Cot[a+b*x]],x] + 1/2*Int[(1-Cot[a+b*x])/Sqrt[c*Cot[a+b*x]],x] /;
FreeQ[{a,b,c},x]


Int[(c_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*c/b*Subst[Int[x^(k*(n+1)-1)/(c^2+x^(2*k)),x],x,(c*Tan[a+b*x])^(1/k)]] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -1<n<1


Int[(c_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  Module[{k=Denominator[n]},
  -k*c/b*Subst[Int[x^(k*(n+1)-1)/(c^2+x^(2*k)),x],x,(c*Cot[a+b*x])^(1/k)]] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -1<n<1


Int[(c_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Tan[a+b*x])^(n+1)/(b*c*(n+1))*Hypergeometric2F1[1,(n+1)/2,(n+3)/2,-Tan[a+b*x]^2] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n]]


Int[(c_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Cot[a+b*x])^(n+1)/(b*c*(n+1))*Hypergeometric2F1[1,(n+1)/2,(n+3)/2,-Cot[a+b*x]^2] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n]]


(* ::Subsection::Closed:: *)
(*2 (a+b tan)^n*)


Int[(a_+b_.*tan[c_.+d_.*x_])^2,x_Symbol] :=
  (a^2-b^2)*x + b^2*Tan[c+d*x]/d + 2*a*b*Int[Tan[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*cot[c_.+d_.*x_])^2,x_Symbol] :=
  (a^2-b^2)*x - b^2*Cot[c+d*x]/d + 2*a*b*Int[Cot[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[c+d*x])^(n-1)/(d*(n-1)) + 
  2*a*Int[(a+b*Tan[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[c+d*x])^(n-1)/(d*(n-1)) + 
  2*a*Int[(a+b*Cot[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a+b*Tan[c+d*x])^n/(2*b*d*n) + 
  1/(2*a)*Int[(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(a+b*Cot[c+d*x])^n/(2*b*d*n) + 
  1/(2*a)*Int[(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -2*b/d*Subst[Int[1/(2*a-x^2),x],x,Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  2*b/d*Subst[Int[1/(2*a-x^2),x],x,Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -b/d*Subst[Int[(a+x)^(n-1)/(a-x),x],x,b*Tan[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && RationalQ[n] && 0<n<1


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b/d*Subst[Int[(a+x)^(n-1)/(a-x),x],x,b*Cot[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && RationalQ[n] && 0<n<1


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Tan[c+d*x])^n/(2*a*d*n)*Hypergeometric2F1[1,n,n+1,(a+b*Tan[c+d*x])/(2*a)] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Cot[c+d*x])^n/(2*a*d*n)*Hypergeometric2F1[1,n,n+1,(a+b*Cot[c+d*x])/(2*a)] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[c+d*x])^(n-1)/(d*(n-1)) + 
  Int[(a^2-b^2+2*a*b*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[c+d*x])^(n-1)/(d*(n-1)) + 
  Int[(a^2-b^2+2*a*b*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[1/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a*x/(a^2+b^2) + b/(a^2+b^2)*Int[(b-a*Tan[c+d*x])/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[1/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  a*x/(a^2+b^2) + b/(a^2+b^2)*Int[(b-a*Cot[c+d*x])/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a-b*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[c+d*x])^(n+1)/(d*(a^2+b^2)*(n+1)) + 
  1/(a^2+b^2)*Int[(a-b*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  (a-b*I)/2*Int[(1+I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] +
  (a+b*I)/2*Int[(1-I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  (a-b*I)/2*Int[(1+I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] +
  (a+b*I)/2*Int[(1-I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2*Int[(1+I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] + 
  1/2*Int[(1-I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2*Int[(1+I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] + 
  1/2*Int[(1-I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]]


(* ::Subsection::Closed:: *)
(*3 (a+b tan)^m (c+d tan)^n*)


Int[(a_+b_.*tan[e_.+f_.*x_])*(c_+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (a*c-b*d)*x + b*d*Tan[e+f*x]/f /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[b*c+a*d]


Int[(a_+b_.*cot[e_.+f_.*x_])*(c_+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (a*c-b*d)*x - b*d*Cot[e+f*x]/f /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[b*c+a*d]


Int[(a_+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (a*c-b*d)*x + b*d*Tan[e+f*x]/f + (b*c+a*d)*Int[Tan[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*c+a*d]


Int[(a_+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (a*c-b*d)*x - b*d*Cot[e+f*x]/f + (b*c+a*d)*Int[Cot[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*c+a*d]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_.*(c_+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  d*(a+b*Tan[e+f*x])^m/(f*m) /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_.*(c_+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -d*(a+b*Cot[e+f*x])^m/(f*m) /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^2,x_Symbol] :=
  d^2*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)) + 
  2*c*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && NonzeroQ[m+1]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^2,x_Symbol] :=
  -d^2*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)) + 
  2*c*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && NonzeroQ[m+1]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(2*a*f*m) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && ZeroQ[m+n]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(2*a*f*m) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && ZeroQ[m+n]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a*c/f*Subst[Int[(a+b*x)^(m-1)*(c+d*x)^(n-1),x],x,Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && NonzeroQ[m+n] && IntegersQ[m,n]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*c/f*Subst[Int[(a+b*x)^(m-1)*(c+d*x)^(n-1),x],x,Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && NonzeroQ[m+n] && IntegersQ[m,n]


Int[1/(Sqrt[a_+b_.*tan[e_.+f_.*x_]]*Sqrt[c_+d_.*tan[e_.+f_.*x_]]),x_Symbol] :=
  Tan[e+f*x]/(f*Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2]


Int[1/(Sqrt[a_+b_.*cot[e_.+f_.*x_]]*Sqrt[c_+d_.*cot[e_.+f_.*x_]]),x_Symbol] :=
  -Cot[e+f*x]/(f*Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^n/(f*n) - 
  b*(m-1)/(d*n)*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && IntegersQ[2*m,2*n] && m>1/2 && n<-1/2 && 
  Not[NegativeIntegerQ[m+n]]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^n/(f*n) - 
  b*(m-1)/(d*n)*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && IntegersQ[2*m,2*n] && m>1/2 && n<-1/2 && 
  Not[NegativeIntegerQ[m+n]]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^n/(f*(m+n-1)) + 
  2*a*(m-1)/(m+n-1)*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && RationalQ[m] && m>1/2 && Not[RationalQ[n] && n<-1/2] && 
  (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[PositiveIntegerQ[n] && n<m] && NonzeroQ[m+n-1]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^n/(f*(m+n-1)) + 
  2*a*(m-1)/(m+n-1)*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && RationalQ[m] && m>1/2 && Not[RationalQ[n] && n<-1/2] && 
  (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[PositiveIntegerQ[n] && n<m] && NonzeroQ[m+n-1]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(2*a*f*m) + 
  (m+n)/(2*a*m)*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && IntegersQ[2*m] && m<-1/2 && RationalQ[n] 


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(2*a*f*m) + 
  (m+n)/(2*a*m)*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && IntegersQ[2*m] && m<-1/2 && RationalQ[n]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a*c/f*Subst[Int[(a+b*x)^(m-1)*(c+d*x)^(n-1),x],x,Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && NonzeroQ[m+n]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*c/f*Subst[Int[(a+b*x)^(m-1)*(c+d*x)^(n-1),x],x,Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && NonzeroQ[m+n]


(* Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(2*a*f*n)*Hypergeometric2F1[1,m+n,n+1,(a-b*Tan[e+f*x])/(2*a)] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && NonzeroQ[m+n] *)


(* Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(2*a*f*n)*Hypergeometric2F1[1,m+n,n+1,(a-b*Cot[e+f*x])/(2*a)] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && NonzeroQ[m+n] *)


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*(a+b*Tan[e+f*x])^m/(2*a*f*m) + 
  (b*c+a*d)/(2*a*b)*Int[(a+b*Tan[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[b*c+a*d] && RationalQ[m] && m<0


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*(a+b*Cot[e+f*x])^m/(2*a*f*m) + 
  (b*c+a*d)/(2*a*b)*Int[(a+b*Cot[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[b*c+a*d] && RationalQ[m] && m<0


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  d*(a+b*Tan[e+f*x])^m/(f*m) + (b*c+a*d)/b*Int[(a+b*Tan[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[b*c+a*d] && Not[RationalQ[m] && m<0]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -d*(a+b*Cot[e+f*x])^m/(f*m) + (b*c+a*d)/b*Int[(a+b*Cot[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[b*c+a*d] && Not[RationalQ[m] && m<0]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  d*(a+b*Tan[e+f*x])^m/(f*m) + 
  Int[(a+b*Tan[e+f*x])^(m-1)*Simp[a*c-b*d+(b*c+a*d)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -d*(a+b*Cot[e+f*x])^m/(f*m) + 
  Int[(a+b*Cot[e+f*x])^(m-1)*Simp[a*c-b*d+(b*c+a*d)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[(c_+d_.*tan[e_.+f_.*x_])/(a_+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  c/(b*f)*Log[RemoveContent[a*Cos[e+f*x]+b*Sin[e+f*x],x]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && ZeroQ[a*c+b*d]


Int[(c_+d_.*cot[e_.+f_.*x_])/(a_+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -c/(b*f)*Log[RemoveContent[b*Cos[e+f*x]+a*Sin[e+f*x],x]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && ZeroQ[a*c+b*d]


Int[(c_.+d_.*tan[e_.+f_.*x_])/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (a*c+b*d)*x/(a^2+b^2) + (b*c-a*d)/(a^2+b^2)*Int[(b-a*Tan[e+f*x])/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[a*c+b*d]


Int[(c_.+d_.*cot[e_.+f_.*x_])/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (a*c+b*d)*x/(a^2+b^2) + (b*c-a*d)/(a^2+b^2)*Int[(b-a*Cot[e+f*x])/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[a*c+b*d]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*(a+b*Tan[e+f*x])^(m+1)/(f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[a*c+b*d-(b*c-a*d)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*(a+b*Cot[e+f*x])^(m+1)/(f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[a*c+b*d-(b*c-a*d)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  c*d/f*Subst[Int[(a+b/d*x)^m/(d^2+c*x),x],x,d*Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && ZeroQ[c^2+d^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -c*d/f*Subst[Int[(a+b/d*x)^m/(d^2+c*x),x],x,d*Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && ZeroQ[c^2+d^2]


Int[(c_+d_.*tan[e_.+f_.*x_])/Sqrt[b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  -2*d^2/f*Subst[Int[1/(2*c*d+b*x^2),x],x,(c-d*Tan[e+f*x])/Sqrt[b*Tan[e+f*x]]] /;
FreeQ[{b,c,d,e,f},x] && ZeroQ[c^2-d^2]


Int[(c_+d_.*cot[e_.+f_.*x_])/Sqrt[b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  2*d^2/f*Subst[Int[1/(2*c*d+b*x^2),x],x,(c-d*Cot[e+f*x])/Sqrt[b*Cot[e+f*x]]] /;
FreeQ[{b,c,d,e,f},x] && ZeroQ[c^2-d^2]


Int[(c_+d_.*tan[e_.+f_.*x_])/Sqrt[b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  (c+d)/2*Int[(1+Tan[e+f*x])/Sqrt[b*Tan[e+f*x]],x] + 
  (c-d)/2*Int[(1-Tan[e+f*x])/Sqrt[b*Tan[e+f*x]],x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[c^2+d^2] && NonzeroQ[c^2-d^2]


Int[(c_+d_.*cot[e_.+f_.*x_])/Sqrt[b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  (c+d)/2*Int[(1+Cot[e+f*x])/Sqrt[b*Cot[e+f*x]],x] + 
  (c-d)/2*Int[(1-Cot[e+f*x])/Sqrt[b*Cot[e+f*x]],x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[c^2+d^2] && NonzeroQ[c^2-d^2]


Int[(b_.*tan[e_.+f_.*x_])^m_*(c_+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  c*Int[(b*Tan[e+f*x])^m,x] + d/b*Int[(b*Tan[e+f*x])^(m+1),x] /;
FreeQ[{b,c,d,e,f,m},x] && NonzeroQ[c^2+d^2] && Not[IntegerQ[2*m]]


Int[(b_.*cot[e_.+f_.*x_])^m_*(c_+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  c*Int[(b*Cot[e+f*x])^m,x] + d/b*Int[(b*Cot[e+f*x])^(m+1),x] /;
FreeQ[{b,c,d,e,f,m},x] && NonzeroQ[c^2+d^2] && Not[IntegerQ[2*m]]


Int[(c_.+d_.*tan[e_.+f_.*x_])/Sqrt[a_.+b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  -2*d^2/f*Subst[Int[1/(2*b*c*d-4*a*d^2+x^2),x],x,(b*c-2*a*d-b*d*Tan[e+f*x])/Sqrt[a+b*Tan[e+f*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && ZeroQ[2*a*c*d-b*(c^2-d^2)]


Int[(c_.+d_.*cot[e_.+f_.*x_])/Sqrt[a_.+b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  2*d^2/f*Subst[Int[1/(2*b*c*d-4*a*d^2+x^2),x],x,(b*c-2*a*d-b*d*Cot[e+f*x])/Sqrt[a+b*Cot[e+f*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && ZeroQ[2*a*c*d-b*(c^2-d^2)]


Int[(c_.+d_.*tan[e_.+f_.*x_])/Sqrt[a_.+b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  1/(2*Rt[a^2+b^2,2])*Int[(a*c+b*d+c*Rt[a^2+b^2,2]+(b*c-a*d+d*Rt[a^2+b^2,2])*Tan[e+f*x])/Sqrt[a+b*Tan[e+f*x]],x] - 
  1/(2*Rt[a^2+b^2,2])*Int[(a*c-c*Rt[a^2+b^2,2]+b*d+(b*c-a*d-d*Rt[a^2+b^2,2])*Tan[e+f*x])/Sqrt[a+b*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && NonzeroQ[2*a*c*d-b*(c^2-d^2)] && 
  (PerfectSquareQ[a^2+b^2] || RationalQ[a,b,c,d])


Int[(c_.+d_.*cot[e_.+f_.*x_])/Sqrt[a_.+b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  1/(2*Rt[a^2+b^2,2])*Int[(a*c+b*d+c*Rt[a^2+b^2,2]+(b*c-a*d+d*Rt[a^2+b^2,2])*Cot[e+f*x])/Sqrt[a+b*Cot[e+f*x]],x] - 
  1/(2*Rt[a^2+b^2,2])*Int[(a*c-c*Rt[a^2+b^2,2]+b*d+(b*c-a*d-d*Rt[a^2+b^2,2])*Cot[e+f*x])/Sqrt[a+b*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && NonzeroQ[2*a*c*d-b*(c^2-d^2)] && 
  (PerfectSquareQ[a^2+b^2] || RationalQ[a,b,c,d])


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (c+I*d)/2*Int[(a+b*Tan[e+f*x])^m*(1-I*Tan[e+f*x]),x] + 
  (c-I*d)/2*Int[(a+b*Tan[e+f*x])^m*(1+I*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[IntegerQ[m]]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (c+I*d)/2*Int[(a+b*Cot[e+f*x])^m*(1-I*Cot[e+f*x]),x] + 
  (c-I*d)/2*Int[(a+b*Cot[e+f*x])^m*(1+I*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[IntegerQ[m]]


Int[tan[e_.+f_.*x_]^2/(a_+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  Log[RemoveContent[a+b*Tan[e+f*x],x]]/(b*f) - Int[1/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,e,f},x]


Int[cot[e_.+f_.*x_]^2/(a_+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -Log[RemoveContent[a+b*Cot[e+f*x],x]]/(b*f) - Int[1/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,e,f},x]


Int[(c_.+d_.*tan[e_.+f_.*x_])^2/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  d*(2*b*c-a*d)*x/b^2 + d^2/b*Int[Tan[e+f*x],x] + (b*c-a*d)^2/b^2*Int[1/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2]


Int[(c_.+d_.*cot[e_.+f_.*x_])^2/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  d*(2*b*c-a*d)*x/b^2 + d^2/b*Int[Cot[e+f*x],x] + (b*c-a*d)^2/b^2*Int[1/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^2,x_Symbol] :=
  (b*c-a*d)^2*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[a*c^2+2*b*c*d-a*d^2-(b*c^2-2*a*c*d-b*d^2)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^2,x_Symbol] :=
  -(b*c-a*d)^2*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[a*c^2+2*b*c*d-a*d^2-(b*c^2-2*a*c*d-b*d^2)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^2,x_Symbol] :=
  d^2*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)) + 
  Int[(a+b*Tan[e+f*x])^m*Simp[c^2-d^2+2*c*d*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && Not[RationalQ[m] && m<=-1]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^2,x_Symbol] :=
  -d^2*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)) + 
  Int[(a+b*Cot[e+f*x])^m*Simp[c^2-d^2+2*c*d*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && Not[RationalQ[m] && m<=-1]


Int[Sqrt[a_+b_.*tan[e_.+f_.*x_]]/Sqrt[c_.+d_.*tan[e_.+f_.*x_]],x_Symbol] :=
  -2*a*b/f*Subst[Int[1/(a*c-b*d-2*a^2*x^2),x],x,Sqrt[c+d*Tan[e+f*x]]/Sqrt[a+b*Tan[e+f*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_+b_.*cot[e_.+f_.*x_]]/Sqrt[c_.+d_.*cot[e_.+f_.*x_]],x_Symbol] :=
  2*a*b/f*Subst[Int[1/(a*c-b*d-2*a^2*x^2),x],x,Sqrt[c+d*Cot[e+f*x]]/Sqrt[a+b*Cot[e+f*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a*b*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)/(f*(m-1)*(a*c-b*d)) + 
  2*a^2/(a*c-b*d)*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m+n==0 && m>1/2


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*b*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)/(f*(m-1)*(a*c-b*d)) + 
  2*a^2/(a*c-b*d)*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m+n==0 && m>1/2


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(2*b*f*m) - 
  (a*c-b*d)/(2*b^2)*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m+n==0 && m<=-1/2


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(2*b*f*m) - 
  (a*c-b*d)/(2*b^2)*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m+n==0 && m<=-1/2


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a)*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m+n+1==0 && m<-1


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a)*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m+n+1==0 && m<-1


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(f*m*(c^2+d^2)) + 
  a/(a*c-b*d)*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && ZeroQ[m+n+1] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  d*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(f*m*(c^2+d^2)) + 
  a/(a*c-b*d)*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && ZeroQ[m+n+1] && Not[RationalQ[m] && m<-1]


Int[Sqrt[a_+b_.*tan[e_.+f_.*x_]]*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  2*d*Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])^(n-1)/(f*(2*n-1)) - 
  1/(a*(2*n-1))*Int[Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])^(n-2)*
    Simp[d*(b*c+2*a*d*(n-1))-a*c^2*(2*n-1)+d*(b*d-a*c*(4*n-3))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*cot[e_.+f_.*x_]]*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*d*Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])^(n-1)/(f*(2*n-1)) - 
  1/(a*(2*n-1))*Int[Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])^(n-2)*
    Simp[d*(b*c+2*a*d*(n-1))-a*c^2*(2*n-1)+d*(b*d-a*c*(4*n-3))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*tan[e_.+f_.*x_]]/(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  a/(a*c-b*d)*Int[Sqrt[a+b*Tan[e+f*x]],x] - 
  d/(a*c-b*d)*Int[Sqrt[a+b*Tan[e+f*x]]*(b+a*Tan[e+f*x])/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_+b_.*cot[e_.+f_.*x_]]/(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  a/(a*c-b*d)*Int[Sqrt[a+b*Cot[e+f*x]],x] - 
  d/(a*c-b*d)*Int[Sqrt[a+b*Cot[e+f*x]]*(b+a*Cot[e+f*x])/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_+b_.*tan[e_.+f_.*x_]]*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  d*Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) - 
  1/(2*a*(n+1)*(c^2+d^2))*Int[Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])^(n+1)*
    Simp[b*d-2*a*c*(n+1)+a*d*(2*n+3)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*cot[e_.+f_.*x_]]*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) - 
  1/(2*a*(n+1)*(c^2+d^2))*Int[Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])^(n+1)*
    Simp[b*d-2*a*c*(n+1)+a*d*(2*n+3)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*tan[e_.+f_.*x_]]*Sqrt[c_.+d_.*tan[e_.+f_.*x_]],x_Symbol] :=
  (a*c-b*d)/a*Int[Sqrt[a+b*Tan[e+f*x]]/Sqrt[c+d*Tan[e+f*x]],x] + 
  d/a*Int[Sqrt[a+b*Tan[e+f*x]]*(b+a*Tan[e+f*x])/Sqrt[c+d*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_+b_.*cot[e_.+f_.*x_]]*Sqrt[c_.+d_.*cot[e_.+f_.*x_]],x_Symbol] :=
  (a*c-b*d)/a*Int[Sqrt[a+b*Cot[e+f*x]]/Sqrt[c+d*Cot[e+f*x]],x] + 
  d/a*Int[Sqrt[a+b*Cot[e+f*x]]*(b+a*Cot[e+f*x])/Sqrt[c+d*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


(* Int[(e_.*tan[e_.+f_.*x_])^m_*Sqrt[a_+b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  -b*e/a*Int[(e*Tan[e+f*x])^(m-1)*Sqrt[a+b*Tan[e+f*x]],x] - 
  e/b*Int[(e*Tan[e+f*x])^(m-1)*(a-b*Tan[e+f*x])*Sqrt[a+b*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && 0<m<1 *)


(* Int[(e_.*cot[e_.+f_.*x_])^m_*Sqrt[a_+b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  -b*e/a*Int[(e*Cot[e+f*x])^(m-1)*Sqrt[a+b*Cot[e+f*x]],x] - 
  e/b*Int[(e*Cot[e+f*x])^(m-1)*(a-b*Cot[e+f*x])*Sqrt[a+b*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && 0<m<1 *)


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  -a^2*(b*c-a*d)*(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^(n+1)/(d*f*(b*c+a*d)*(n+1)) + 
  a/(d*(b*c+a*d)*(n+1))*Int[(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^(n+1)*
    Simp[b*(b*c*(m-2)-a*d*(m-2*n-4))+(a*b*c*(m-2)+b^2*d*(n+1)-a^2*d*(m+n-1))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>1 && n<-1 && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*(b*c-a*d)*(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^(n+1)/(d*f*(b*c+a*d)*(n+1)) + 
  a/(d*(b*c+a*d)*(n+1))*Int[(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^(n+1)*
    Simp[b*(b*c*(m-2)-a*d*(m-2*n-4))+(a*b*c*(m-2)+b^2*d*(n+1)-a^2*d*(m+n-1))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>1 && n<-1 && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*tan[e_.+f_.*x_])^(3/2)/(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  2*a^2/(a*c-b*d)*Int[Sqrt[a+b*Tan[e+f*x]],x] - 
  (2*b*c*d+a*(c^2-d^2))/(a*(c^2+d^2))*Int[(a-b*Tan[e+f*x])*Sqrt[a+b*Tan[e+f*x]]/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_+b_.*cot[e_.+f_.*x_])^(3/2)/(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  2*a^2/(a*c-b*d)*Int[Sqrt[a+b*Cot[e+f*x]],x] - 
  (2*b*c*d+a*(c^2-d^2))/(a*(c^2+d^2))*Int[(a-b*Cot[e+f*x])*Sqrt[a+b*Cot[e+f*x]]/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_+b_.*tan[e_.+f_.*x_])^(3/2)/Sqrt[c_.+d_.*tan[e_.+f_.*x_]],x_Symbol] :=
  2*a*Int[Sqrt[a+b*Tan[e+f*x]]/Sqrt[c+d*Tan[e+f*x]],x] + 
  b/a*Int[(b+a*Tan[e+f*x])*Sqrt[a+b*Tan[e+f*x]]/Sqrt[c+d*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_+b_.*cot[e_.+f_.*x_])^(3/2)/Sqrt[c_.+d_.*cot[e_.+f_.*x_]],x_Symbol] :=
  2*a*Int[Sqrt[a+b*Cot[e+f*x]]/Sqrt[c+d*Cot[e+f*x]],x] + 
  b/a*Int[(b+a*Cot[e+f*x])*Sqrt[a+b*Cot[e+f*x]]/Sqrt[c+d*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^(n+1)/(d*f*(m+n-1)) + 
  a/(d*(m+n-1))*Int[(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^n*
    Simp[b*c*(m-2)+a*d*(m+2*n)+(a*c*(m-2)+b*d*(3*m+2*n-4))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  IntegerQ[2*m] && m>1 && NonzeroQ[m+n-1] && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^(n+1)/(d*f*(m+n-1)) + 
  a/(d*(m+n-1))*Int[(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^n*
    Simp[b*c*(m-2)+a*d*(m+2*n)+(a*c*(m-2)+b*d*(3*m+2*n-4))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  IntegerQ[2*m] && m>1 && NonzeroQ[m+n-1] && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_/(a_+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  -(a*c+b*d)*(c+d*Tan[e+f*x])^n/(2*(b*c-a*d)*f*(a+b*Tan[e+f*x])) + 
  1/(2*a*(b*c-a*d))*Int[(c+d*Tan[e+f*x])^(n-1)*Simp[a*c*d*(n-1)+b*c^2+b*d^2*n-d*(b*c-a*d)*(n-1)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && 0<n<1


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_/(a_+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (a*c+b*d)*(c+d*Cot[e+f*x])^n/(2*(b*c-a*d)*f*(a+b*Cot[e+f*x])) + 
  1/(2*a*(b*c-a*d))*Int[(c+d*Cot[e+f*x])^(n-1)*Simp[a*c*d*(n-1)+b*c^2+b*d^2*n-d*(b*c-a*d)*(n-1)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && 0<n<1


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_/(a_+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*(c+d*Tan[e+f*x])^(n-1)/(2*a*f*(a+b*Tan[e+f*x])) + 
  1/(2*a^2)*Int[(c+d*Tan[e+f*x])^(n-2)*Simp[a*c^2+a*d^2*(n-1)-b*c*d*n-d*(a*c*(n-2)+b*d*n)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && n>1


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_/(a_+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*(c+d*Cot[e+f*x])^(n-1)/(2*a*f*(a+b*Cot[e+f*x])) + 
  1/(2*a^2)*Int[(c+d*Cot[e+f*x])^(n-2)*Simp[a*c^2+a*d^2*(n-1)-b*c*d*n-d*(a*c*(n-2)+b*d*n)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && n>1


Int[1/((a_.+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*Tan[e+f*x]),x] - d/(b*c-a*d)*Int[1/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[1/((a_.+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*Cot[e+f*x]),x] - d/(b*c-a*d)*Int[1/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_/(a_+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  -a*(c+d*Tan[e+f*x])^(n+1)/(2*f*(b*c-a*d)*(a+b*Tan[e+f*x])) + 
  1/(2*a*(b*c -a*d))*Int[(c+d*Tan[e+f*x])^n*Simp[b*c+a*d*(n-1)-b*d*n*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n>0]


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_/(a_+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  a*(c+d*Cot[e+f*x])^(n+1)/(2*f*(b*c-a*d)*(a+b*Cot[e+f*x])) + 
  1/(2*a*(b*c -a*d))*Int[(c+d*Cot[e+f*x])^n*Simp[b*c+a*d*(n-1)-b*d*n*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n>0]


Int[(c_.+d_.*tan[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  (b*c-a*d)*Sqrt[c+d*Tan[e+f*x]]/(a*f*Sqrt[a+b*Tan[e+f*x]]) - 
  1/(2*a^2)*Int[Sqrt[a+b*Tan[e+f*x]]*Simp[2*b*c*d-a*(c^2+d^2)+2*b*d^2*Tan[e+f*x],x]/Sqrt[c+d*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(c_.+d_.*cot[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  -(b*c-a*d)*Sqrt[c+d*Cot[e+f*x]]/(a*f*Sqrt[a+b*Cot[e+f*x]]) - 
  1/(2*a^2)*Int[Sqrt[a+b*Cot[e+f*x]]*Simp[2*b*c*d-a*(c^2+d^2)+2*b*d^2*Cot[e+f*x],x]/Sqrt[c+d*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[1/(Sqrt[a_+b_.*tan[e_.+f_.*x_]]*(c_.+d_.*tan[e_.+f_.*x_])),x_Symbol] :=
  -a/((b*c-a*d)*f*Sqrt[a+b*Tan[e+f*x]]) + 
  1/(2*a*(b*c-a*d))*Int[Sqrt[a+b*Tan[e+f*x]]*Simp[b*c-2*a*d+b*d*Tan[e+f*x],x]/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[1/(Sqrt[a_+b_.*cot[e_.+f_.*x_]]*(c_.+d_.*cot[e_.+f_.*x_])),x_Symbol] :=
  a/((b*c-a*d)*f*Sqrt[a+b*Cot[e+f*x]]) + 
  1/(2*a*(b*c-a*d))*Int[Sqrt[a+b*Cot[e+f*x]]*Simp[b*c-2*a*d+b*d*Cot[e+f*x],x]/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[1/(Sqrt[a_+b_.*tan[e_.+f_.*x_]]*Sqrt[c_.+d_.*tan[e_.+f_.*x_]]),x_Symbol] :=
  -a*Sqrt[c+d*Tan[e+f*x]]/((b*c-a*d)*f*Sqrt[a+b*Tan[e+f*x]]) + 
  1/(2*a)*Int[Sqrt[a+b*Tan[e+f*x]]/Sqrt[c+d*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[1/(Sqrt[a_+b_.*cot[e_.+f_.*x_]]*Sqrt[c_.+d_.*cot[e_.+f_.*x_]]),x_Symbol] :=
  a*Sqrt[c+d*Cot[e+f*x]]/((b*c-a*d)*f*Sqrt[a+b*Cot[e+f*x]]) + 
  1/(2*a)*Int[Sqrt[a+b*Cot[e+f*x]]/Sqrt[c+d*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_/Sqrt[a_+b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  d*(c+d*Tan[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)*Sqrt[a+b*Tan[e+f*x]]) + 
  1/(2*a*(n+1)*(c^2+d^2))*Int[(c+d*Tan[e+f*x])^(n+1)*Simp[b*d+2*a*c*(n+1)-a*d*(2*n+1)*Tan[e+f*x],x]/Sqrt[a+b*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_/Sqrt[a_+b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  -d*(c+d*Cot[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)*Sqrt[a+b*Cot[e+f*x]]) + 
  1/(2*a*(n+1)*(c^2+d^2))*Int[(c+d*Cot[e+f*x])^(n+1)*Simp[b*d+2*a*c*(n+1)-a*d*(2*n+1)*Cot[e+f*x],x]/Sqrt[a+b*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*Sqrt[c_.+d_.*tan[e_.+f_.*x_]],x_Symbol] :=
  -b*(a+b*Tan[e+f*x])^m*Sqrt[c+d*Tan[e+f*x]]/(2*a*f*m) + 
  1/(4*a^2*m)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[2*a*c*m+b*d+a*d*(2*m+1)*Tan[e+f*x],x]/Sqrt[c+d*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m<-1 && IntegersQ[2*m]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*Sqrt[c_.+d_.*cot[e_.+f_.*x_]],x_Symbol] :=
  b*(a+b*Cot[e+f*x])^m*Sqrt[c+d*Cot[e+f*x]]/(2*a*f*m) + 
  1/(4*a^2*m)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[2*a*c*m+b*d+a*d*(2*m+1)*Cot[e+f*x],x]/Sqrt[c+d*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m<-1 && IntegersQ[2*m]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b*c-a*d)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n-1)/(2*a*f*m) + 
  1/(2*a^2*m)*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^(n-2)*
    Simp[c*(a*c*m+b*d*(n-1))-d*(b*c*m+a*d*(n-1))-d*(b*d*(m-n+1)-a*c*(m+n-1))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  RationalQ[m,n] && m<-1 && n>1 && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*c-a*d)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n-1)/(2*a*f*m) + 
  1/(2*a^2*m)*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^(n-2)*
    Simp[c*(a*c*m+b*d*(n-1))-d*(b*c*m+a*d*(n-1))-d*(b*d*(m-n+1)-a*c*(m+n-1))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  RationalQ[m,n] && m<-1 && n>1 && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a*m*(b*c-a*d))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n*
    Simp[b*c*m-a*d*(2*m+n+1)+b*d*(m+n+1)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  RationalQ[m] && m<-1 && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a*m*(b*c-a*d))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n*
    Simp[b*c*m-a*d*(2*m+n+1)+b*d*(m+n+1)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  RationalQ[m] && m<-1 && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  d*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n-1)/(f*(m+n-1)) - 
  1/(a*(m+n-1))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n-2)*
    Simp[d*(b*c*m+a*d*(-1+n))-a*c^2*(m+n-1)+d*(b*d*m-a*c*(m+2*n-2))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  RationalQ[n] && n>1 && NonzeroQ[m+n-1] && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(c_.+d_.*cot[e_.+f_.*x_])^m_*(a_+b_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n-1)/(f*(m+n-1)) - 
  1/(a*(m+n-1))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n-2)*
    Simp[d*(b*c*m+a*d*(-1+n))-a*c^2*(m+n-1)+d*(b*d*m-a*c*(m+2*n-2))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  RationalQ[n] && n>1 && NonzeroQ[m+n-1] && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(a_+b_.*tan[e_.+f_.*x_])^m_/(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  a/(a*c-b*d)*Int[(a+b*Tan[e+f*x])^m,x] - 
  d/(a*c-b*d)*Int[(a+b*Tan[e+f*x])^m*(b+a*Tan[e+f*x])/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_/(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  a/(a*c-b*d)*Int[(a+b*Cot[e+f*x])^m,x] - 
  d/(a*c-b*d)*Int[(a+b*Cot[e+f*x])^m*(b+a*Cot[e+f*x])/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  d*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) - 
  1/(a*(c^2+d^2)*(n+1))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)*
    Simp[b*d*m-a*c*(n+1)+a*d*(m+n+1)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  RationalQ[n] && n<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) - 
  1/(a*(c^2+d^2)*(n+1))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)*
    Simp[b*d*m-a*c*(n+1)+a*d*(m+n+1)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  RationalQ[n] && n<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a*b/f*Subst[Int[(a+x)^(m-1)*(c+d/b*x)^n/(b^2+a*x),x],x,b*Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[IntegerQ[m]]


Int[(c_.+d_.*cot[e_.+f_.*x_])^m_*(a_+b_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*b/f*Subst[Int[(a+x)^(m-1)*(c+d/b*x)^n/(b^2+a*x),x],x,b*Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[IntegerQ[m]]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*c-a*d)^2*(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(d*(n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^(m-3)*(c+d*Tan[e+f*x])^(n+1)*
    Simp[a^2*d*(b*d*(m-2)-a*c*(n+1))+b*(b*c-2*a*d)*(b*c*(m-2)+a*d*(n+1)) - 
    d*(n+1)*(3*a^2*b*c-b^3*c-a^3*d+3*a*b^2*d)*Tan[e+f*x] - 
    b*(a*d*(2*b*c-a*d)*(m+n-1)-b^2*(c^2*(m-2)-d^2*(n+1)))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>2 && n<-1


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b*c-a*d)^2*(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(d*(n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^(m-3)*(c+d*Cot[e+f*x])^(n+1)*
    Simp[a^2*d*(b*d*(m-2)-a*c*(n+1))+b*(b*c-2*a*d)*(b*c*(m-2)+a*d*(n+1)) - 
    d*(n+1)*(3*a^2*b*c-b^3*c-a^3*d+3*a*b^2*d)*Cot[e+f*x] - 
    b*(a*d*(2*b*c-a*d)*(m+n-1)-b^2*(c^2*(m-2)-d^2*(n+1)))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>2 && n<-1


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^(n+1)/(d*f*(m+n-1)) + 
  1/(d*(m+n-1))*Int[(a+b*Tan[e+f*x])^(m-3)*(c+d*Tan[e+f*x])^n*
    Simp[a^3*d*(m+n-1)-b^2*(b*c*(m-2)+a*d*(1+n))+b*d*(m+n-1)*(3*a^2-b^2)*Tan[e+f*x]-b^2*(b*c*(m-2)-a*d*(3*m+2*n-4))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  IntegerQ[2*m] && m>2 && (RationalQ[n] && n>=-1 || IntegerQ[m]) && (IntegerQ[2*m] || IntegerQ[n])


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^(n+1)/(d*f*(m+n-1)) + 
  1/(d*(m+n-1))*Int[(a+b*Cot[e+f*x])^(m-3)*(c+d*Cot[e+f*x])^n*
    Simp[a^3*d*(m+n-1)-b^2*(b*c*(m-2)+a*d*(1+n))+b*d*(m+n-1)*(3*a^2-b^2)*Cot[e+f*x]-b^2*(b*c*(m-2)-a*d*(3*m+2*n-4))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  IntegerQ[2*m] && m>2 && (RationalQ[n] && n>=-1 || IntegerQ[m]) && (IntegerQ[2*m] || IntegerQ[n])


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b*c-a*d)*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) + 
  1/((n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^(n+1)*
    Simp[b^2*c*(m-1)-a*b*d*(m-n-2)+a^2*c*(n+1)+(2*a*b*c-a^2*d+b^2*d)*(n+1)*Tan[e+f*x]+b*(b*c-a*d)*(m+n)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && 1<m<2 && n<-1 && IntegerQ[2*n]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*c-a*d)*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) + 
  1/((n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^(n+1)*
    Simp[b^2*c*(m-1)-a*b*d*(m-n-2)+a^2*c*(n+1)+(2*a*b*c-a^2*d+b^2*d)*(n+1)*Cot[e+f*x]+b*(b*c-a*d)*(m+n)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && 1<m<2 && n<-1 && IntegerQ[2*n]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  d*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) - 
  1/((n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)*
    Simp[b*d*m-a*c*(n+1)-(b*c-a*d)*(n+1)*Tan[e+f*x]+b*d*(m+n+1)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>0 && n<-1 && IntegerQ[2*n]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) - 
  1/((n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)*
    Simp[b*d*m-a*c*(n+1)-(b*c-a*d)*(n+1)*Cot[e+f*x]+b*d*(m+n+1)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>0 && n<-1 && IntegerQ[2*n]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^(n+1)/(f*(m+1)*(a^2+b^2)*(b*c-a*d)) + 
  1/((m+1)*(a^2+b^2)*(b*c-a*d))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n*
    Simp[a*(b*c-a*d)*(m+1)-b^2*d*(m+n+2)-b*(b*c-a*d)*(m+1)*Tan[e+f*x]-b^2*d*(m+n+2)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  IntegerQ[2*m] && m<-1 && (RationalQ[n] && n<0 || IntegerQ[m])


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^(n+1)/(f*(m+1)*(a^2+b^2)*(b*c-a*d)) + 
  1/((m+1)*(a^2+b^2)*(b*c-a*d))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n*
    Simp[a*(b*c-a*d)*(m+1)-b^2*d*(m+n+2)-b*(b*c-a*d)*(m+1)*Cot[e+f*x]-b^2*d*(m+n+2)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  IntegerQ[2*m] && m<-1 && (RationalQ[n] && n<0 || IntegerQ[m])


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^n/(f*(m+n-1)) + 
  1/(m+n-1)*Int[(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^(n-1)*
    Simp[a^2*c*(m+n-1)-b*(b*c*(m-1)+a*d*n)+(2*a*b*c+a^2*d-b^2*d)*(m+n-1)*Tan[e+f*x]+b*(b*c*n+a*d*(2*m+n-2))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>1 && n>0 && IntegerQ[2*n]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^n/(f*(m+n-1)) + 
  1/(m+n-1)*Int[(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^(n-1)*
    Simp[a^2*c*(m+n-1)-b*(b*c*(m-1)+a*d*n)+(2*a*b*c+a^2*d-b^2*d)*(m+n-1)*Cot[e+f*x]+b*(b*c*n+a*d*(2*m+n-2))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>1 && n>0 && IntegerQ[2*n]


Int[1/((a_+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])),x_Symbol] :=
  (a*c-b*d)*x/((a^2+b^2)*(c^2+d^2)) + 
  b^2/((b*c-a*d)*(a^2+b^2))*Int[(b-a*Tan[e+f*x])/(a+b*Tan[e+f*x]),x] - 
  d^2/((b*c-a*d)*(c^2+d^2))*Int[(d-c*Tan[e+f*x])/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[1/((a_+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])),x_Symbol] :=
  (a*c-b*d)*x/((a^2+b^2)*(c^2+d^2)) + 
  b^2/((b*c-a*d)*(a^2+b^2))*Int[(b-a*Cot[e+f*x])/(a+b*Cot[e+f*x]),x] - 
  d^2/((b*c-a*d)*(c^2+d^2))*Int[(d-c*Cot[e+f*x])/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_.+b_.*tan[e_.+f_.*x_]]/(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  1/(c^2+d^2)*Int[Simp[a*c+b*d+(b*c-a*d)*Tan[e+f*x],x]/Sqrt[a+b*Tan[e+f*x]],x] - 
  d*(b*c-a*d)/(c^2+d^2)*Int[(1+Tan[e+f*x]^2)/(Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_.+b_.*cot[e_.+f_.*x_]]/(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  1/(c^2+d^2)*Int[Simp[a*c+b*d+(b*c-a*d)*Cot[e+f*x],x]/Sqrt[a+b*Cot[e+f*x]],x] - 
  d*(b*c-a*d)/(c^2+d^2)*Int[(1+Cot[e+f*x]^2)/(Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^(3/2)/(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  1/(c^2+d^2)*Int[Simp[a^2*c-b^2*c+2*a*b*d+(2*a*b*c-a^2*d+b^2*d)*Tan[e+f*x],x]/Sqrt[a+b*Tan[e+f*x]],x] + 
  (b*c-a*d)^2/(c^2+d^2)*Int[(1+Tan[e+f*x]^2)/(Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^(3/2)/(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  1/(c^2+d^2)*Int[Simp[a^2*c-b^2*c+2*a*b*d+(2*a*b*c-a^2*d+b^2*d)*Cot[e+f*x],x]/Sqrt[a+b*Cot[e+f*x]],x] + 
  (b*c-a*d)^2/(c^2+d^2)*Int[(1+Cot[e+f*x]^2)/(Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(a-b*Tan[e+f*x])*(c+d*Tan[e+f*x])^n,x] + 
  b^2/(a^2+b^2)*Int[(c+d*Tan[e+f*x])^n*(1+Tan[e+f*x]^2)/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[IntegerQ[n]]


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(a-b*Cot[e+f*x])*(c+d*Cot[e+f*x])^n,x] + 
  b^2/(a^2+b^2)*Int[(c+d*Cot[e+f*x])^n*(1+Cot[e+f*x]^2)/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[IntegerQ[n]]


Int[Sqrt[a_.+b_.*tan[e_.+f_.*x_]]*Sqrt[c_+d_.*tan[e_.+f_.*x_]],x_Symbol] :=
  Int[Simp[a*c-b*d+(b*c+a*d)*Tan[e+f*x],x]/(Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]),x] + 
  b*d*Int[(1+Tan[e+f*x]^2)/(Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_.+b_.*cot[e_.+f_.*x_]]*Sqrt[c_+d_.*cot[e_.+f_.*x_]],x_Symbol] :=
  Int[Simp[a*c-b*d+(b*c+a*d)*Cot[e+f*x],x]/(Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]),x] + 
  b*d*Int[(1+Cot[e+f*x]^2)/(Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_.+b_.*tan[e_.+f_.*x_]]*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  -(I*a+b)/2*Int[(c+d*Tan[e+f*x])^n*(I-Tan[e+f*x])/Sqrt[a+b*Tan[e+f*x]],x] - 
  (I*a-b)/2*Int[(c+d*Tan[e+f*x])^n*(I+Tan[e+f*x])/Sqrt[a+b*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && (n>0 || n<=-1)]


Int[Sqrt[a_.+b_.*cot[e_.+f_.*x_]]*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  -(I*a+b)/2*Int[(c+d*Cot[e+f*x])^n*(I-Cot[e+f*x])/Sqrt[a+b*Cot[e+f*x]],x] - 
  (I*a-b)/2*Int[(c+d*Cot[e+f*x])^n*(I+Cot[e+f*x])/Sqrt[a+b*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && (n>0 || n<=-1)]


Int[(a_.+b_.*tan[e_.+f_.*x_])^(3/2)/Sqrt[c_.+d_.*tan[e_.+f_.*x_]],x_Symbol] :=
  Int[Simp[a^2-b^2+2*a*b*Tan[e+f*x],x]/(Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]),x] + 
  b^2*Int[(1+Tan[e+f*x]^2)/(Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^(3/2)/Sqrt[c_.+d_.*cot[e_.+f_.*x_]],x_Symbol] :=
  Int[Simp[a^2-b^2+2*a*b*Cot[e+f*x],x]/(Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]),x] + 
  b^2*Int[(1+Cot[e+f*x]^2)/(Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  1/2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*(1-I*Tan[e+f*x]),x] + 
  1/2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*(1+I*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[IntegerQ[m]]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_,x_Symbol] :=
  1/2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*(1-I*Cot[e+f*x]),x] + 
  1/2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*(1+I*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[IntegerQ[m]]


(* ::Subsection::Closed:: *)
(*4 (a+b tan)^m (c+d tan)^n (A+B tan)*)


Int[(c_.+d_.*tan[e_.+f_.*x_])*(A_.+B_.*tan[e_.+f_.*x_])/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  B*d/b*Int[Tan[e+f*x],x] + 1/b*Int[Simp[A*b*c+(A*b*d+B*(b*c-a*d))*Tan[e+f*x],x]/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d]


Int[(c_.+d_.*cot[e_.+f_.*x_])*(A_.+B_.*cot[e_.+f_.*x_])/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  B*d/b*Int[Cot[e+f*x],x] + 1/b*Int[Simp[A*b*c+(A*b*d+B*(b*c-a*d))*Cot[e+f*x],x]/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*(a*c+b*d)*(a+b*Tan[e+f*x])^m/(2*a^2*f*m) + 
  1/(2*a*b)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[A*b*c+a*B*c+a*A*d+b*B*d+2*a*B*d*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && RationalQ[m] && m<-1 && ZeroQ[a^2+b^2]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*(a*c+b*d)*(a+b*Cot[e+f*x])^m/(2*a^2*f*m) + 
  1/(2*a*b)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[A*b*c+a*B*c+a*A*d+b*B*d+2*a*B*d*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && RationalQ[m] && m<-1 && ZeroQ[a^2+b^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*(A*b-a*B)*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[a*A*c+b*B*c+A*b*d-a*B*d-(A*b*c-a*B*c-a*A*d-b*B*d)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && RationalQ[m] && m<-1 && NonzeroQ[a^2+b^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*(A*b-a*B)*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[a*A*c+b*B*c+A*b*d-a*B*d-(A*b*c-a*B*c-a*A*d-b*B*d)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && RationalQ[m] && m<-1 && NonzeroQ[a^2+b^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  B*d*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)) + 
  Int[(a+b*Tan[e+f*x])^m*Simp[A*c-B*d+(B*c+A*d)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && Not[RationalQ[m] && m<=-1]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -B*d*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)) + 
  Int[(a+b*Cot[e+f*x])^m*Simp[A*c-B*d+(B*c+A*d)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && Not[RationalQ[m] && m<=-1]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_.*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(2*a*f*m) + 
  (A*b*(m+n)+a*B*(m-n))/(2*a*b*m)*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && RationalQ[m] && m<-1


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(2*a*f*m) + 
  (A*b*(m+n)+a*B*(m-n))/(2*a*b*m)*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && RationalQ[m] && m<-1


Int[(a_+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  B*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(f*(m+n)) + 
  (A*b*(m+n)+a*B*(m-n))/(b*(m+n))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -B*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(f*(m+n)) + 
  (A*b*(m+n)+a*B*(m-n))/(b*(m+n))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[c^2+d^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  -a^2*(B*c-A*d)*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)/(d*f*(b*c+a*d)*(n+1)) - 
  a/(d*(b*c+a*d)*(n+1))*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)*
    Simp[A*b*d*(m-n-2)-B*(b*c*(m-1)+a*d*(n+1))+(a*A*d*(m+n)-B*(a*c*(m-1)+b*d*(n+1)))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m,n] && m>1 && n<-1


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  a^2*(B*c-A*d)*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)/(d*f*(b*c+a*d)*(n+1)) - 
  a/(d*(b*c+a*d)*(n+1))*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)*
    Simp[A*b*d*(m-n-2)-B*(b*c*(m-1)+a*d*(n+1))+(a*A*d*(m+n)-B*(a*c*(m-1)+b*d*(n+1)))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m,n] && m>1 && n<-1


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  b*B*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^n*
    Simp[a*A*d*(m+n)+B*(a*c*(m-1)-b*d*(n+1))-(B*(b*c-a*d)*(m-1)-d*(A*b+a*B)*(m+n))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m] && m>1 && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -b*B*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^n*
    Simp[a*A*d*(m+n)+B*(a*c*(m-1)-b*d*(n+1))-(B*(b*c-a*d)*(m-1)-d*(A*b+a*B)*(m+n))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m] && m>1 && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(2*a*f*m) + 
  1/(2*a^2*m)*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^(n-1)*
    Simp[A*(a*c*m+b*d*n)-B*(b*c*m+a*d*n)-d*(b*B*(m-n)-a*A*(m+n))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m,n] && m<0 && n>0


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(2*a*f*m) + 
  1/(2*a^2*m)*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^(n-1)*
    Simp[A*(a*c*m+b*d*n)-B*(b*c*m+a*d*n)-d*(b*B*(m-n)-a*A*(m+n))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m,n] && m<0 && n>0


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (a*A+b*B)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a*m*(b*c-a*d))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n*
    Simp[A*(b*c*m-a*d*(2*m+n+1))+B*(a*c*m-b*d*(n+1))+d*(A*b-a*B)*(m+n+1)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m] && m<0 && Not[RationalQ[n] && n>0]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -(a*A+b*B)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a*m*(b*c-a*d))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n*
    Simp[A*(b*c*m-a*d*(2*m+n+1))+B*(a*c*m-b*d*(n+1))+d*(A*b-a*B)*(m+n+1)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m] && m<0 && Not[RationalQ[n] && n>0]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  B*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(f*(m+n)) + 
  1/(a*(m+n))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n-1)*
    Simp[a*A*c*(m+n)-B*(b*c*m+a*d*n)+(a*A*d*(m+n)-B*(b*d*m-a*c*n))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[n] && n>0


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -B*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(f*(m+n)) + 
  1/(a*(m+n))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n-1)*
    Simp[a*A*c*(m+n)-B*(b*c*m+a*d*n)+(a*A*d*(m+n)-B*(b*d*m-a*c*n))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[n] && n>0


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (A*d-B*c)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) - 
  1/(a*(n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)*
    Simp[A*(b*d*m-a*c*(n+1))-B*(b*c*m+a*d*(n+1))-a*(B*c-A*d)*(m+n+1)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -(A*d-B*c)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(f*(n+1)*(c^2+d^2)) - 
  1/(a*(n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)*
    Simp[A*(b*d*m-a*c*(n+1))-B*(b*c*m+a*d*(n+1))-a*(B*c-A*d)*(m+n+1)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  b*B/f*Subst[Int[(a+b*x)^(m-1)*(c+d*x)^n,x],x,Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -b*B/f*Subst[Int[(a+b*x)^(m-1)*(c+d*x)^n,x],x,Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(A_.+B_.*tan[e_.+f_.*x_])/(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (A*b+a*B)/(b*c+a*d)*Int[(a+b*Tan[e+f*x])^m,x] - 
  (B*c-A*d)/(b*c+a*d)*Int[(a+b*Tan[e+f*x])^m*(a-b*Tan[e+f*x])/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(A_.+B_.*cot[e_.+f_.*x_])/(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (A*b+a*B)/(b*c+a*d)*Int[(a+b*Cot[e+f*x])^m,x] - 
  (B*c-A*d)/(b*c+a*d)*Int[(a+b*Cot[e+f*x])^m*(a-b*Cot[e+f*x])/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B]


(* Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n,x] + 
  B/b*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] *)


(* Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n,x] + 
  B/b*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] *)


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (A*b+a*B)/b*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n,x] - 
  B/b*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*(a-b*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (A*b+a*B)/b*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n,x] - 
  B/b*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*(a-b*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  A^2/f*Subst[Int[(a+b*x)^m*(c+d*x)^n/(A-B*x),x],x,Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && 
  Not[IntegersQ[2*m,2*n]] && ZeroQ[A^2+B^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -A^2/f*Subst[Int[(a+b*x)^m*(c+d*x)^n/(A-B*x),x],x,Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && 
  Not[IntegersQ[2*m,2*n]] && ZeroQ[A^2+B^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (A+I*B)/2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*(1-I*Tan[e+f*x]),x] + 
  (A-I*B)/2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*(1+I*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && 
  Not[IntegersQ[2*m,2*n]] && NonzeroQ[A^2+B^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (A+I*B)/2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*(1-I*Cot[e+f*x]),x] + 
  (A-I*B)/2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*(1+I*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && 
  Not[IntegersQ[2*m,2*n]] && NonzeroQ[A^2+B^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*(B*c-A*d)*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(d*(n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^(n+1)*
    Simp[a*A*d*(b*d*(m-1)-a*c*(n+1))+(b*B*c-(A*b+a*B)*d)*(b*c*(m-1)+a*d*(n+1))-
      d*((a*A-b*B)*(b*c-a*d)+(A*b+a*B)*(a*c+b*d))*(n+1)*Tan[e+f*x]-
      b*(d*(A*b*c+a*B*c-a*A*d)*(m+n)-b*B*(c^2*(m-1)-d^2*(n+1)))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>1 && n<-1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*(B*c-A*d)*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(d*(n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^(n+1)*
    Simp[a*A*d*(b*d*(m-1)-a*c*(n+1))+(b*B*c-(A*b+a*B)*d)*(b*c*(m-1)+a*d*(n+1))-
      d*((a*A-b*B)*(b*c-a*d)+(A*b+a*B)*(a*c+b*d))*(n+1)*Cot[e+f*x]-
      b*(d*(A*b*c+a*B*c-a*A*d)*(m+n)-b*B*(c^2*(m-1)-d^2*(n+1)))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>1 && n<-1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  b*B*(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Tan[e+f*x])^(m-2)*(c+d*Tan[e+f*x])^n*
    Simp[a^2*A*d*(m+n)-b*B*(b*c*(m-1)+a*d*(n+1))+
      d*(m+n)*(2*a*A*b+B*(a^2-b^2))*Tan[e+f*x]-
      (b*B*(b*c-a*d)*(m-1)-b*(A*b+a*B)*d*(m+n))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m>1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -b*B*(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Cot[e+f*x])^(m-2)*(c+d*Cot[e+f*x])^n*
    Simp[a^2*A*d*(m+n)-b*B*(b*c*(m-1)+a*d*(n+1))+
      d*(m+n)*(2*a*A*b+B*(a^2-b^2))*Cot[e+f*x]-
      (b*B*(b*c-a*d)*(m-1)-b*(A*b+a*B)*d*(m+n))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m>1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n/(f*(m+1)*(a^2+b^2)) + 
  1/(b*(m+1)*(a^2+b^2))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^(n-1)*
    Simp[b*B*(b*c*(m+1)+a*d*n)+A*b*(a*c*(m+1)-b*d*n)-b*(A*(b*c-a*d)-B*(a*c+b*d))*(m+1)*Tan[e+f*x]-b*d*(A*b-a*B)*(m+n+1)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m<-1 && 0<n<1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n/(f*(m+1)*(a^2+b^2)) + 
  1/(b*(m+1)*(a^2+b^2))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^(n-1)*
    Simp[b*B*(b*c*(m+1)+a*d*n)+A*b*(a*c*(m+1)-b*d*n)-b*(A*(b*c-a*d)-B*(a*c+b*d))*(m+1)*Cot[e+f*x]-b*d*(A*b-a*B)*(m+n+1)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m<-1 && 0<n<1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  b*(A*b-a*B)*(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2+b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2+b^2))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n*
    Simp[b*B*(b*c*(m+1)+a*d*(n+1))+A*(a*(b*c-a*d)*(m+1)-b^2*d*(m+n+2)) - 
      (A*b-a*B)*(b*c-a*d)*(m+1)*Tan[e+f*x] - 
      b*d*(A*b-a*B)*(m+n+2)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m<-1 && 
  (IntegerQ[m] && NonzeroQ[a] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -b*(A*b-a*B)*(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2+b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2+b^2))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n*
    Simp[b*B*(b*c*(m+1)+a*d*(n+1))+A*(a*(b*c-a*d)*(m+1)-b^2*d*(m+n+2))-
      (A*b-a*B)*(b*c-a*d)*(m+1)*Cot[e+f*x]-
      b*d*(A*b-a*B)*(m+n+2)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m<-1 && 
  (IntegerQ[m] && NonzeroQ[a] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  B*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n/(f*(m+n)) + 
  1/(m+n)*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n-1)*
    Simp[a*A*c*(m+n)-B*(b*c*m+a*d*n)+(A*b*c+a*B*c+a*A*d-b*B*d)*(m+n)*Tan[e+f*x]+(A*b*d*(m+n)+B*(a*d*m+b*c*n))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && 0<m<1 && 0<n<1


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -B*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n/(f*(m+n)) + 
  1/(m+n)*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n-1)*
    Simp[a*A*c*(m+n)-B*(b*c*m+a*d*n)+(A*b*c+a*B*c+a*A*d-b*B*d)*(m+n)*Cot[e+f*x]+(A*b*d*(m+n)+B*(a*d*m+b*c*n))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && 0<m<1 && 0<n<1


Int[(A_.+B_.*tan[e_.+f_.*x_])/((a_+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])),x_Symbol] :=
  (B*(b*c+a*d)+A*(a*c-b*d))*x/((a^2+b^2)*(c^2+d^2)) + 
  b*(A*b-a*B)/((b*c-a*d)*(a^2+b^2))*Int[(b-a*Tan[e+f*x])/(a+b*Tan[e+f*x]),x] + 
  d*(B*c-A*d)/((b*c-a*d)*(c^2+d^2))*Int[(d-c*Tan[e+f*x])/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(A_.+B_.*cot[e_.+f_.*x_])/((a_+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])),x_Symbol] :=
  (B*(b*c+a*d)+A*(a*c-b*d))*x/((a^2+b^2)*(c^2+d^2)) + 
  b*(A*b-a*B)/((b*c-a*d)*(a^2+b^2))*Int[(b-a*Cot[e+f*x])/(a+b*Cot[e+f*x]),x] + 
  d*(B*c-A*d)/((b*c-a*d)*(c^2+d^2))*Int[(d-c*Cot[e+f*x])/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_.+b_.*tan[e_.+f_.*x_]]*(A_.+B_.*tan[e_.+f_.*x_])/(c_.+d_.*tan[e_.+f_.*x_]),x_Symbol] :=
  1/(c^2+d^2)*Int[Simp[A*(a*c+b*d)-B*(b*c-a*d)+(A*(b*c-a*d)+B*(a*c+b*d))*Tan[e+f*x],x]/Sqrt[a+b*Tan[e+f*x]],x] + 
  (b*c-a*d)*(B*c-A*d)/(c^2+d^2)*Int[(1+Tan[e+f*x]^2)/(Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_.+b_.*cot[e_.+f_.*x_]]*(A_.+B_.*cot[e_.+f_.*x_])/(c_.+d_.*cot[e_.+f_.*x_]),x_Symbol] :=
  1/(c^2+d^2)*Int[Simp[A*(a*c+b*d)-B*(b*c-a*d)+(A*(b*c-a*d)+B*(a*c+b*d))*Cot[e+f*x],x]/Sqrt[a+b*Cot[e+f*x]],x] + 
  (b*c-a*d)*(B*c-A*d)/(c^2+d^2)*Int[(1+Cot[e+f*x]^2)/(Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_])/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(c+d*Tan[e+f*x])^n*Simp[a*A+b*B-(A*b-a*B)*Tan[e+f*x],x],x] + 
  b*(A*b-a*B)/(a^2+b^2)*Int[(c+d*Tan[e+f*x])^n*(1+Tan[e+f*x]^2)/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_])/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(c+d*Cot[e+f*x])^n*Simp[a*A+b*B-(A*b-a*B)*Cot[e+f*x],x],x] + 
  b*(A*b-a*B)/(a^2+b^2)*Int[(c+d*Cot[e+f*x])^n*(1+Cot[e+f*x]^2)/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_.+b_.*tan[e_.+f_.*x_]]*(A_.+B_.*tan[e_.+f_.*x_])/Sqrt[c_.+d_.*tan[e_.+f_.*x_]],x_Symbol] :=
  Int[Simp[a*A-b*B+(A*b+a*B)*Tan[e+f*x],x]/(Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]),x] + 
  b*B*Int[(1+Tan[e+f*x]^2)/(Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[Sqrt[a_.+b_.*cot[e_.+f_.*x_]]*(A_.+B_.*cot[e_.+f_.*x_])/Sqrt[c_.+d_.*cot[e_.+f_.*x_]],x_Symbol] :=
  Int[Simp[a*A-b*B+(A*b+a*B)*Cot[e+f*x],x]/(Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]),x] + 
  b*B*Int[(1+Cot[e+f*x]^2)/(Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(A_.+B_.*tan[e_.+f_.*x_])/(Sqrt[a_.+b_.*tan[e_.+f_.*x_]]*Sqrt[c_.+d_.*tan[e_.+f_.*x_]]),x_Symbol] :=
  A^2/f*Subst[Int[1/((A-B*x)*Sqrt[a+b*x]*Sqrt[c+d*x]),x],x,Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && ZeroQ[A^2+B^2]


Int[(A_.+B_.*cot[e_.+f_.*x_])/(Sqrt[a_.+b_.*cot[e_.+f_.*x_]]*Sqrt[c_.+d_.*cot[e_.+f_.*x_]]),x_Symbol] :=
  -A^2/f*Subst[Int[1/((A-B*x)*Sqrt[a+b*x]*Sqrt[c+d*x]),x],x,Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && ZeroQ[A^2+B^2]


Int[(A_.+B_.*tan[e_.+f_.*x_])/(Sqrt[a_.+b_.*tan[e_.+f_.*x_]]*Sqrt[c_.+d_.*tan[e_.+f_.*x_]]),x_Symbol] :=
  (A+I*B)/2*Int[(1-I*Tan[e+f*x])/(Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]),x] + 
  (A-I*B)/2*Int[(1+I*Tan[e+f*x])/(Sqrt[a+b*Tan[e+f*x]]*Sqrt[c+d*Tan[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && NonzeroQ[A^2+B^2]


Int[(A_.+B_.*cot[e_.+f_.*x_])/(Sqrt[a_.+b_.*cot[e_.+f_.*x_]]*Sqrt[c_.+d_.*cot[e_.+f_.*x_]]),x_Symbol] :=
  (A+I*B)/2*Int[(1-I*Cot[e+f*x])/(Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]),x] + 
  (A-I*B)/2*Int[(1+I*Cot[e+f*x])/(Sqrt[a+b*Cot[e+f*x]]*Sqrt[c+d*Cot[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && NonzeroQ[A^2+B^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  A^2/f*Subst[Int[(a+b*x)^m*(c+d*x)^n/(A-B*x),x],x,Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  -A^2/f*Subst[Int[(a+b*x)^m*(c+d*x)^n/(A-B*x),x],x,Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (A+I*B)/2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*(1-I*Tan[e+f*x]),x] + 
  (A-I*B)/2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*(1+I*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[A^2+B^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (A+I*B)/2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*(1-I*Cot[e+f*x]),x] + 
  (A-I*B)/2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*(1+I*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[A^2+B^2]


(* ::Subsection::Closed:: *)
(*5 (a+b tan)^m (A+B tan+C tan^2)*)


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(A_+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  A/f*Subst[Int[(a+b*x)^m,x],x,Tan[e+f*x]] /;
FreeQ[{a,b,e,f,A,C,m},x] && ZeroQ[A-C]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -A/f*Subst[Int[(a+b*x)^m,x],x,Cot[e+f*x]] /;
FreeQ[{a,b,e,f,A,C,m},x] && ZeroQ[A-C]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  1/b^2*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[b*B-a*C+b*C*Tan[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  1/b^2*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[b*B-a*C+b*C*Cot[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  -C/b^2*Int[(a+b*Tan[e+f*x])^(m+1)*(a-b*Tan[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,C,m},x] && ZeroQ[A*b^2+a^2*C]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -C/b^2*Int[(a+b*Cot[e+f*x])^(m+1)*(a-b*Cot[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,C,m},x] && ZeroQ[A*b^2+a^2*C]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A+b*B-a*C)*Tan[e+f*x]*(a+b*Tan[e+f*x])^m/(2*a*f*m) + 
  1/(2*a^2*m)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[(b*B-a*C)+a*A*(2*m+1)-(b*C*(m-1)+(A*b-a*B)*(m+1))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<=-1 && ZeroQ[a^2+b^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A+b*B-a*C)*Cot[e+f*x]*(a+b*Cot[e+f*x])^m/(2*a*f*m) + 
  1/(2*a^2*m)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[(b*B-a*C)+a*A*(2*m+1)-(b*C*(m-1)+(A*b-a*B)*(m+1))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<=-1 && ZeroQ[a^2+b^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A-a*C)*Tan[e+f*x]*(a+b*Tan[e+f*x])^m/(2*a*f*m) + 
  1/(2*a^2*m)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[-a*C+a*A*(2*m+1)-(b*C*(m-1)+A*b*(m+1))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[m] && m<=-1 && ZeroQ[a^2+b^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A-a*C)*Cot[e+f*x]*(a+b*Cot[e+f*x])^m/(2*a*f*m) + 
  1/(2*a^2*m)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[-a*C+a*A*(2*m+1)-(b*C*(m-1)+A*b*(m+1))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[m] && m<=-1 && ZeroQ[a^2+b^2]


Int[(A_+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2)/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (a*A+b*B-a*C)*x/(a^2+b^2) + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(1+Tan[e+f*x]^2)/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2+b^2] && ZeroQ[A*b-a*B-b*C]


Int[(A_+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2)/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (a*A+b*B-a*C)*x/(a^2+b^2) + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(1+Cot[e+f*x]^2)/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2+b^2] && ZeroQ[A*b-a*B-b*C]


Int[(A_+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2)/tan[e_.+f_.*x_],x_Symbol] :=
  B*x+A*Int[1/Tan[e+f*x],x] + C*Int[Tan[e+f*x],x] /;
FreeQ[{e,f,A,B,C},x] && NonzeroQ[A-C]


Int[(A_+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2)/cot[e_.+f_.*x_],x_Symbol] :=
  B*x+A*Int[1/Cot[e+f*x],x] + C*Int[Cot[e+f*x],x] /;
FreeQ[{e,f,A,B,C},x] && NonzeroQ[A-C]


Int[(A_+C_.*tan[e_.+f_.*x_]^2)/tan[e_.+f_.*x_],x_Symbol] :=
  A*Int[1/Tan[e+f*x],x] + C*Int[Tan[e+f*x],x] /;
FreeQ[{e,f,A,C},x] && NonzeroQ[A-C]


Int[(A_+C_.*cot[e_.+f_.*x_]^2)/cot[e_.+f_.*x_],x_Symbol] :=
  A*Int[1/Cot[e+f*x],x] + C*Int[Cot[e+f*x],x] /;
FreeQ[{e,f,A,C},x] && NonzeroQ[A-C]


Int[(A_+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2)/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  (a*A+b*B-a*C)*x/(a^2+b^2) - 
  (A*b-a*B-b*C)/(a^2+b^2)*Int[Tan[e+f*x],x] + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(1+Tan[e+f*x]^2)/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && NonzeroQ[a^2+b^2] && NonzeroQ[A*b-a*B-b*C]


Int[(A_+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2)/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  (a*A+b*B-a*C)*x/(a^2+b^2) - 
  (A*b-a*B-b*C)/(a^2+b^2)*Int[Cot[e+f*x],x] + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(1+Cot[e+f*x]^2)/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && NonzeroQ[a^2+b^2] && NonzeroQ[A*b-a*B-b*C]


Int[(A_+C_.*tan[e_.+f_.*x_]^2)/(a_+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  a*(A-C)*x/(a^2+b^2) - 
  b*(A-C)/(a^2+b^2)*Int[Tan[e+f*x],x] + 
  (a^2*C+A*b^2)/(a^2+b^2)*Int[(1+Tan[e+f*x]^2)/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2*C+A*b^2] && NonzeroQ[a^2+b^2] && NonzeroQ[A-C]


Int[(A_+C_.*cot[e_.+f_.*x_]^2)/(a_+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  a*(A-C)*x/(a^2+b^2) - 
  b*(A-C)/(a^2+b^2)*Int[Cot[e+f*x],x] + 
  (a^2*C+A*b^2)/(a^2+b^2)*Int[(1+Cot[e+f*x]^2)/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2*C+A*b^2] && NonzeroQ[a^2+b^2] && NonzeroQ[A-C]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[b*B+a*(A-C)-(A*b-a*B-b*C)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<-1 && NonzeroQ[a^2+b^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[b*B+a*(A-C)-(A*b-a*B-b*C)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<-1 && NonzeroQ[a^2+b^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Tan[e+f*x])^(m+1)*Simp[a*(A-C)-(A*b-b*C)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[m] && m<-1 && NonzeroQ[a^2+b^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a+b*Cot[e+f*x])^(m+1)*Simp[a*(A-C)-(A*b-b*C)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[m] && m<-1 && NonzeroQ[a^2+b^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  C*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)) + Int[(a+b*Tan[e+f*x])^m*Simp[A-C+B*Tan[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && Not[RationalQ[m] && m<=-1]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -C*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)) + Int[(a+b*Cot[e+f*x])^m*Simp[A-C+B*Cot[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && Not[RationalQ[m] && m<=-1]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  C*(a+b*Tan[e+f*x])^(m+1)/(b*f*(m+1)) + (A-C)*Int[(a+b*Tan[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[A*b^2+a^2*C] && Not[RationalQ[m] && m<=-1]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -C*(a+b*Cot[e+f*x])^(m+1)/(b*f*(m+1)) + (A-C)*Int[(a+b*Cot[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[A*b^2+a^2*C] && Not[RationalQ[m] && m<=-1]


(* ::Subsection::Closed:: *)
(*6 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2)*)


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_.*(A_+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  A/f*Subst[Int[(a+b*x)^m*(c+d*x)^n,x],x,Tan[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && ZeroQ[A-C]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -A/f*Subst[Int[(a+b*x)^m*(c+d*x)^n,x],x,Cot[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && ZeroQ[A-C]


Int[(a_.+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  -(b*c-a*d)*(c^2*C-B*c*d+A*d^2)*(c+d*Tan[e+f*x])^(n+1)/(d^2*f*(n+1)*(c^2+d^2)) + 
  1/(d*(c^2+d^2))*Int[(c+d*Tan[e+f*x])^(n+1)*
    Simp[a*d*(A*c-c*C+B*d)+b*(c^2*C-B*c*d+A*d^2)+d*(A*b*c+a*B*c-b*c*C-a*A*d+b*B*d+a*C*d)*Tan[e+f*x]+b*C*(c^2+d^2)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[c^2+d^2] && RationalQ[n] && n<-1


Int[(a_.+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  (b*c-a*d)*(c^2*C-B*c*d+A*d^2)*(c+d*Cot[e+f*x])^(n+1)/(d^2*f*(n+1)*(c^2+d^2)) + 
  1/(d*(c^2+d^2))*Int[(c+d*Cot[e+f*x])^(n+1)*
    Simp[a*d*(A*c-c*C+B*d)+b*(c^2*C-B*c*d+A*d^2)+d*(A*b*c+a*B*c-b*c*C-a*A*d+b*B*d+a*C*d)*Cot[e+f*x]+b*C*(c^2+d^2)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[c^2+d^2] && RationalQ[n] && n<-1


Int[(a_.+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  -(b*c-a*d)*(c^2*C+A*d^2)*(c+d*Tan[e+f*x])^(n+1)/(d^2*f*(n+1)*(c^2+d^2)) + 
  1/(d*(c^2+d^2))*Int[(c+d*Tan[e+f*x])^(n+1)*
    Simp[a*d*(A*c-c*C)+b*(c^2*C+A*d^2)+d*(A*b*c-b*c*C-a*A*d+a*C*d)*Tan[e+f*x]+b*C*(c^2+d^2)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[c^2+d^2] && RationalQ[n] && n<-1


Int[(a_.+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  (b*c-a*d)*(c^2*C+A*d^2)*(c+d*Cot[e+f*x])^(n+1)/(d^2*f*(n+1)*(c^2+d^2)) + 
  1/(d*(c^2+d^2))*Int[(c+d*Cot[e+f*x])^(n+1)*
    Simp[a*d*(A*c-c*C)+b*(c^2*C+A*d^2)+d*(A*b*c-b*c*C-a*A*d+a*C*d)*Cot[e+f*x]+b*C*(c^2+d^2)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[c^2+d^2] && RationalQ[n] && n<-1


Int[(a_+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])^n_.*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  b*C*Tan[e+f*x]*(c+d*Tan[e+f*x])^(n+1)/(d*f*(n+2)) - 
  1/(d*(n+2))*Int[(c+d*Tan[e+f*x])^n*
    Simp[b*c*C-a*A*d*(n+2)-(A*b+a*B-b*C)*d*(n+2)*Tan[e+f*x]-(a*C*d*(n+2)-b*(c*C-B*d*(n+2)))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Cot[e+f*x]*(c+d*Cot[e+f*x])^(n+1)/(d*f*(n+2)) - 
  1/(d*(n+2))*Int[(c+d*Cot[e+f*x])^n*
    Simp[b*c*C-a*A*d*(n+2)-(A*b+a*B-b*C)*d*(n+2)*Cot[e+f*x]-(a*C*d*(n+2)-b*(c*C-B*d*(n+2)))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])^n_.*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  b*C*Tan[e+f*x]*(c+d*Tan[e+f*x])^(n+1)/(d*f*(n+2)) - 
  1/(d*(n+2))*Int[(c+d*Tan[e+f*x])^n*
    Simp[b*c*C-a*A*d*(n+2)-(A*b-b*C)*d*(n+2)*Tan[e+f*x]-(a*C*d*(n+2)-b*c*C)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Cot[e+f*x]*(c+d*Cot[e+f*x])^(n+1)/(d*f*(n+2)) - 
  1/(d*(n+2))*Int[(c+d*Cot[e+f*x])^n*
    Simp[b*c*C-a*A*d*(n+2)-(A*b-b*C)*d*(n+2)*Cot[e+f*x]-(a*C*d*(n+2)-b*c*C)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_.*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A+b*B-a*C)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a*m*(b*c-a*d))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n*
    Simp[b*(c*(A+C)*m-B*d*(n+1))+a*(B*c*m+C*d*(n+1)-A*d*(2*m+n+1))+
      (b*C*d*(m-n-1)+A*b*d*(m+n+1)+a*(2*c*C*m-B*d*(m+n+1)))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A+b*B-a*C)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a*m*(b*c-a*d))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n*
    Simp[b*(c*(A+C)*m-B*d*(n+1))+a*(B*c*m+C*d*(n+1)-A*d*(2*m+n+1))+
      (b*C*d*(m-n-1)+A*b*d*(m+n+1)+a*(2*c*C*m-B*d*(m+n+1)))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_.*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A-C)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a*m*(b*c-a*d))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n*
    Simp[b*c*(A+C)*m+a*(C*d*(n+1)-A*d*(2*m+n+1))+(b*C*d*(m-n-1)+A*b*d*(m+n+1)+2*a*c*C*m)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A-C)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(2*f*m*(b*c-a*d)) + 
  1/(2*a*m*(b*c-a*d))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n*
    Simp[b*c*(A+C)*m+a*(C*d*(n+1)-A*d*(2*m+n+1))+(b*C*d*(m-n-1)+A*b*d*(m+n+1)+2*a*c*C*m)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (c^2*C-B*c*d+A*d^2)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(a*d*(n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)*
    Simp[b*(c^2*C-B*c*d+A*d^2)*m-a*d*(n+1)*(A*c-c*C+B*d)-a*(d*(B*c-A*d)*(m+n+1)-C*(c^2*m-d^2*(n+1)))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && Not[RationalQ[m] && m<-1] && RationalQ[n] && n<-1 && 
  NonzeroQ[c^2+d^2]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C-B*c*d+A*d^2)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(a*d*(n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)*
    Simp[b*(c^2*C-B*c*d+A*d^2)*m-a*d*(n+1)*(A*c-c*C+B*d)-a*(d*(B*c-A*d)*(m+n+1)-C*(c^2*m-d^2*(n+1)))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && Not[RationalQ[m] && m<-1] && RationalQ[n] && n<-1 && 
  NonzeroQ[c^2+d^2]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (c^2*C+A*d^2)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(a*d*(n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)*
    Simp[b*(c^2*C+A*d^2)*m-a*d*(n+1)*(A*c-c*C)-a*(-A*d^2*(m+n+1)-C*(c^2*m-d^2*(n+1)))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && Not[RationalQ[m] && m<-1] && RationalQ[n] && n<-1 && 
  NonzeroQ[c^2+d^2]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C+A*d^2)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(a*d*(n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)*
    Simp[b*(c^2*C+A*d^2)*m-a*d*(n+1)*(A*c-c*C)-a*(-A*d^2*(m+n+1)-C*(c^2*m-d^2*(n+1)))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && Not[RationalQ[m] && m<-1] && RationalQ[n] && n<-1 && 
  NonzeroQ[c^2+d^2]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_.*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  C*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(b*d*(m+n+1))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*
    Simp[A*b*d*(m+n+1)+C*(a*c*m-b*d*(n+1))-(C*m*(b*c-a*d)-b*B*d*(m+n+1))*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n+1]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -C*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(b*d*(m+n+1))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*
    Simp[A*b*d*(m+n+1)+C*(a*c*m-b*d*(n+1))-(C*m*(b*c-a*d)-b*B*d*(m+n+1))*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n+1]


Int[(a_+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_.*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  C*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(b*d*(m+n+1))*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*
    Simp[A*b*d*(m+n+1)+C*(a*c*m-b*d*(n+1))-C*m*(b*c-a*d)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n+1]


Int[(a_+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -C*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(b*d*(m+n+1))*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*
    Simp[A*b*d*(m+n+1)+C*(a*c*m-b*d*(n+1))-C*m*(b*c-a*d)*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2+b^2] && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n+1]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (A*d^2+c*(c*C-B*d))*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(d*(n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m-a*c*(n+1))+(c*C-B*d)*(b*c*m+a*d*(n+1)) - 
      d*(n+1)*((A-C)*(b*c-a*d)+B*(a*c+b*d))*Tan[e+f*x] - 
      b*(d*(B*c-A*d)*(m+n+1)-C*(c^2*m-d^2*(n+1)))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*d^2+c*(c*C-B*d))*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(d*(n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m-a*c*(n+1))+(c*C-B*d)*(b*c*m+a*d*(n+1)) - 
      d*(n+1)*((A-C)*(b*c-a*d)+B*(a*c+b*d))*Cot[e+f*x] - 
      b*(d*(B*c-A*d)*(m+n+1)-C*(c^2*m-d^2*(n+1)))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (A*d^2+c^2*C)*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(d*(n+1)*(c^2+d^2))*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m-a*c*(n+1))+c*C*(b*c*m+a*d*(n+1)) - 
      d*(n+1)*((A-C)*(b*c-a*d))*Tan[e+f*x] + 
      b*(A*d^2*(m+n+1)+C*(c^2*m-d^2*(n+1)))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*d^2+c^2*C)*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(d*f*(n+1)*(c^2+d^2)) - 
  1/(d*(n+1)*(c^2+d^2))*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m-a*c*(n+1))+c*C*(b*c*m+a*d*(n+1)) - 
      d*(n+1)*((A-C)*(b*c-a*d))*Cot[e+f*x] + 
      b*(A*d^2*(m+n+1)+C*(c^2*m-d^2*(n+1)))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  C*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^n*
    Simp[a*A*d*(m+n+1)-C*(b*c*m+a*d*(n+1))+d*(A*b+a*B-b*C)*(m+n+1)*Tan[e+f*x]-(C*m*(b*c-a*d)-b*B*d*(m+n+1))*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -C*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^n*
    Simp[a*A*d*(m+n+1)-C*(b*c*m+a*d*(n+1))+d*(A*b+a*B-b*C)*(m+n+1)*Cot[e+f*x]-(C*m*(b*c-a*d)-b*B*d*(m+n+1))*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  C*(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Tan[e+f*x])^(m-1)*(c+d*Tan[e+f*x])^n*
    Simp[a*A*d*(m+n+1)-C*(b*c*m+a*d*(n+1))+d*(A*b-b*C)*(m+n+1)*Tan[e+f*x]-C*m*(b*c-a*d)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -C*(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Cot[e+f*x])^(m-1)*(c+d*Cot[e+f*x])^n*
    Simp[a*A*d*(m+n+1)-C*(b*c*m+a*d*(n+1))+d*(A*b-b*C)*(m+n+1)*Cot[e+f*x]-C*m*(b*c-a*d)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*(b*B-a*C))*(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2+b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2+b^2))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n*
     Simp[A*(a*(b*c -a*d)*(m+1)-b^2*d*(m+n+2))+(b*B-a*C)*(b*c*(m+1)+a*d*(n+1)) - 
      (m+1)*(b*c-a*d)*(A*b-a*B-b*C)*Tan[e+f*x] - 
      d*(A*b^2-a*(b*B-a*C))*(m+n+2)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m<-1 &&
  Not[IntegerQ[n] && n<-1 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*(b*B-a*C))*(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2+b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2+b^2))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n*
     Simp[A*(a*(b*c -a*d)*(m+1)-b^2*d*(m+n+2))+(b*B-a*C)*(b*c*(m+1)+a*d*(n+1)) - 
      (m+1)*(b*c-a*d)*(A*b-a*B-b*C)*Cot[e+f*x] - 
      d*(A*b^2-a*(b*B-a*C))*(m+n+2)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m<-1 &&
  Not[IntegerQ[n] && n<-1 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2+b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2+b^2))*Int[(a+b*Tan[e+f*x])^(m+1)*(c+d*Tan[e+f*x])^n*
     Simp[A*(a*(b*c -a*d)*(m+1)-b^2*d*(m+n+2))-a*C*(b*c*(m+1)+a*d*(n+1)) - 
      (m+1)*(b*c-a*d)*(A*b-b*C)*Tan[e+f*x] - 
      d*(A*b^2+a^2*C)*(m+n+2)*Tan[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m<-1 &&
  Not[IntegerQ[n] && n<-1 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2+b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2+b^2))*Int[(a+b*Cot[e+f*x])^(m+1)*(c+d*Cot[e+f*x])^n*
     Simp[A*(a*(b*c -a*d)*(m+1)-b^2*d*(m+n+2))-a*C*(b*c*(m+1)+a*d*(n+1)) - 
      (m+1)*(b*c-a*d)*(A*b-b*C)*Cot[e+f*x] - 
      d*(A*b^2+a^2*C)*(m+n+2)*Cot[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && RationalQ[m] && m<-1 &&
  Not[IntegerQ[n] && n<-1 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2)/((a_+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])),x_Symbol] :=
  (a*(A*c-c*C+B*d)+b*(B*c-A*d+C*d))*x/((a^2+b^2)*(c^2+d^2)) + 
  (A*b^2-a*b*B+a^2*C)/((b*c-a*d)*(a^2+b^2))*Int[(b-a*Tan[e+f*x])/(a+b*Tan[e+f*x]),x] - 
  (c^2*C-B*c*d+A*d^2)/((b*c-a*d)*(c^2+d^2))*Int[(d-c*Tan[e+f*x])/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2)/((a_+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])),x_Symbol] :=
  (a*(A*c-c*C+B*d)+b*(B*c-A*d+C*d))*x/((a^2+b^2)*(c^2+d^2)) + 
  (A*b^2-a*b*B+a^2*C)/((b*c-a*d)*(a^2+b^2))*Int[(b-a*Cot[e+f*x])/(a+b*Cot[e+f*x]),x] - 
  (c^2*C-B*c*d+A*d^2)/((b*c-a*d)*(c^2+d^2))*Int[(d-c*Cot[e+f*x])/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(A_.+C_.*tan[e_.+f_.*x_]^2)/((a_+b_.*tan[e_.+f_.*x_])*(c_.+d_.*tan[e_.+f_.*x_])),x_Symbol] :=
  (a*(A*c-c*C)-b*(A*d-C*d))*x/((a^2+b^2)*(c^2+d^2)) + 
  (A*b^2+a^2*C)/((b*c-a*d)*(a^2+b^2))*Int[(b-a*Tan[e+f*x])/(a+b*Tan[e+f*x]),x] - 
  (c^2*C+A*d^2)/((b*c-a*d)*(c^2+d^2))*Int[(d-c*Tan[e+f*x])/(c+d*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(A_.+C_.*cot[e_.+f_.*x_]^2)/((a_+b_.*cot[e_.+f_.*x_])*(c_.+d_.*cot[e_.+f_.*x_])),x_Symbol] :=
  (a*(A*c-c*C)-b*(A*d-C*d))*x/((a^2+b^2)*(c^2+d^2)) + 
  (A*b^2+a^2*C)/((b*c-a*d)*(a^2+b^2))*Int[(b-a*Cot[e+f*x])/(a+b*Cot[e+f*x]),x] - 
  (c^2*C+A*d^2)/((b*c-a*d)*(c^2+d^2))*Int[(d-c*Cot[e+f*x])/(c+d*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2)/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(c+d*Tan[e+f*x])^n*Simp[b*B+a*(A-C)+(a*B-b*(A-C))*Tan[e+f*x],x],x] + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(c+d*Tan[e+f*x])^n*(1+Tan[e+f*x]^2)/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  Not[RationalQ[n] && n>0] && Not[RationalQ[n] && n<=-1]


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2)/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(c+d*Cot[e+f*x])^n*Simp[b*B+a*(A-C)+(a*B-b*(A-C))*Cot[e+f*x],x],x] + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(c+d*Cot[e+f*x])^n*(1+Cot[e+f*x]^2)/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  Not[RationalQ[n] && n>0] && Not[RationalQ[n] && n<=-1]


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+C_.*tan[e_.+f_.*x_]^2)/(a_.+b_.*tan[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(c+d*Tan[e+f*x])^n*Simp[a*(A-C)-(A*b-b*C)*Tan[e+f*x],x],x] + 
  (A*b^2+a^2*C)/(a^2+b^2)*Int[(c+d*Tan[e+f*x])^n*(1+Tan[e+f*x]^2)/(a+b*Tan[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  Not[RationalQ[n] && n>0] && Not[RationalQ[n] && n<=-1]


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+C_.*cot[e_.+f_.*x_]^2)/(a_.+b_.*cot[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(c+d*Cot[e+f*x])^n*Simp[a*(A-C)-(A*b-b*C)*Cot[e+f*x],x],x] + 
  (A*b^2+a^2*C)/(a^2+b^2)*Int[(c+d*Cot[e+f*x])^n*(1+Cot[e+f*x]^2)/(a+b*Cot[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && 
  Not[RationalQ[n] && n>0] && Not[RationalQ[n] && n<=-1]


Int[(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*tan[e_.+f_.*x_]]*(c_.+d_.*tan[e_.+f_.*x_])),x_Symbol] :=
  1/(c^2+d^2)*Int[(A*c-c*C+B*d+(B*c-d*(A-C))*Tan[e+f*x])/Sqrt[a+b*Tan[e+f*x]],x] + 
  (c^2*C-B*c*d+A*d^2)/(c^2+d^2)*Int[(1+Tan[e+f*x]^2)/(Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*cot[e_.+f_.*x_]]*(c_.+d_.*cot[e_.+f_.*x_])),x_Symbol] :=
  1/(c^2+d^2)*Int[(A*c-c*C+B*d+(B*c-d*(A-C))*Cot[e+f*x])/Sqrt[a+b*Cot[e+f*x]],x] + 
  (c^2*C-B*c*d+A*d^2)/(c^2+d^2)*Int[(1+Cot[e+f*x]^2)/(Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(A_.+C_.*tan[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*tan[e_.+f_.*x_]]*(c_.+d_.*tan[e_.+f_.*x_])),x_Symbol] :=
  1/(c^2+d^2)*Int[(A*c-c*C-d*(A-C)*Tan[e+f*x])/Sqrt[a+b*Tan[e+f*x]],x] + 
  (c^2*C+A*d^2)/(c^2+d^2)*Int[(1+Tan[e+f*x]^2)/(Sqrt[a+b*Tan[e+f*x]]*(c+d*Tan[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(A_.+C_.*cot[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*cot[e_.+f_.*x_]]*(c_.+d_.*cot[e_.+f_.*x_])),x_Symbol] :=
  1/(c^2+d^2)*Int[(A*c-c*C-d*(A-C)*Cot[e+f*x])/Sqrt[a+b*Cot[e+f*x]],x] + 
  (c^2*C+A*d^2)/(c^2+d^2)*Int[(1+Cot[e+f*x]^2)/(Sqrt[a+b*Cot[e+f*x]]*(c+d*Cot[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2)/Sqrt[a_.+b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  Int[(c+d*Tan[e+f*x])^n*(A-C+B*Tan[e+f*x])/Sqrt[a+b*Tan[e+f*x]],x] + 
  C*Int[(c+d*Tan[e+f*x])^n*(1+Tan[e+f*x]^2)/Sqrt[a+b*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n>0] && 
  Not[RationalQ[n] && n<=-1]


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2)/Sqrt[a_.+b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  Int[(c+d*Cot[e+f*x])^n*(A-C+B*Cot[e+f*x])/Sqrt[a+b*Cot[e+f*x]],x] + 
  C*Int[(c+d*Cot[e+f*x])^n*(1+Cot[e+f*x]^2)/Sqrt[a+b*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n>0] && 
  Not[RationalQ[n] && n<=-1]


Int[(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+C_.*tan[e_.+f_.*x_]^2)/Sqrt[a_.+b_.*tan[e_.+f_.*x_]],x_Symbol] :=
  (A-C)*Int[(c+d*Tan[e+f*x])^n/Sqrt[a+b*Tan[e+f*x]],x] + 
  C*Int[(c+d*Tan[e+f*x])^n*(1+Tan[e+f*x]^2)/Sqrt[a+b*Tan[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n>0] && 
  Not[RationalQ[n] && n<=-1]


Int[(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+C_.*cot[e_.+f_.*x_]^2)/Sqrt[a_.+b_.*cot[e_.+f_.*x_]],x_Symbol] :=
  (A-C)*Int[(c+d*Cot[e+f*x])^n/Sqrt[a+b*Cot[e+f*x]],x] + 
  C*Int[(c+d*Cot[e+f*x])^n*(1+Cot[e+f*x]^2)/Sqrt[a+b*Cot[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2] && Not[RationalQ[n] && n>0] && 
  Not[RationalQ[n] && n<=-1]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+B_.*tan[e_.+f_.*x_]+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  C/d^2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+2),x] - 
  1/d^2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*Simp[c^2*C-A*d^2+d*(2*c*C-B*d)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  C/d^2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+2),x] - 
  1/d^2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*Simp[c^2*C-A*d^2+d*(2*c*C-B*d)*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_.+b_.*tan[e_.+f_.*x_])^m_*(c_.+d_.*tan[e_.+f_.*x_])^n_*(A_.+C_.*tan[e_.+f_.*x_]^2),x_Symbol] :=
  C/d^2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^(n+2),x] - 
  1/d^2*Int[(a+b*Tan[e+f*x])^m*(c+d*Tan[e+f*x])^n*Simp[c^2*C-A*d^2+2*c*C*d*Tan[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


Int[(a_.+b_.*cot[e_.+f_.*x_])^m_*(c_.+d_.*cot[e_.+f_.*x_])^n_*(A_.+C_.*cot[e_.+f_.*x_]^2),x_Symbol] :=
  C/d^2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^(n+2),x] - 
  1/d^2*Int[(a+b*Cot[e+f*x])^m*(c+d*Cot[e+f*x])^n*Simp[c^2*C-A*d^2+2*c*C*d*Cot[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2+b^2] && NonzeroQ[c^2+d^2]


(* ::Subsection::Closed:: *)
(*7 (e trig)^m (a+b tan)^n*)


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  e^(m+1)/d*Subst[Int[x^m*(a+b*e*x)^n/(1+e^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m/2]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  Module[{e=FreeFactors[Cot[c+d*x],x]},
  -e^(m+1)/d*Subst[Int[x^m*(a+b*e*x)^n/(1+e^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m/2]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Expand[Sin[c+d*x]^m*(a+b*Tan[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && PositiveIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Expand[Cos[c+d*x]^m*(a+b*Cot[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && PositiveIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sin[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/Cos[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && NegativeIntegerQ[n] && (m<5 && n>-4 || m==5 && n==-1)


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cos[c+d*x]^m*(a*Sin[c+d*x]+b*Cos[c+d*x])^n/Sin[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && NegativeIntegerQ[n] && (m<5 && n>-4 || m==5 && n==-1)


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  e/d*Subst[Int[(a+b*e*x)^n/(1+e^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m/2]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Module[{e=FreeFactors[Cot[c+d*x],x]},
  -e/d*Subst[Int[(a+b*e*x)^n/(1+e^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m/2]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Expand[Cos[c+d*x]^m*(a+b*Tan[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && PositiveIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Expand[Sin[c+d*x]^m*(a+b*Cot[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && PositiveIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cos[c+d*x]^(m-n)*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && NegativeIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sin[c+d*x]^(m-n)*(a*Sin[c+d*x]+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && NegativeIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^p_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cos[c+d*x]^(m-n)*Sin[c+d*x]^p*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,p},x] && IntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*cos[c_.+d_.*x_]^p_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sin[c+d*x]^(m-n)*Cos[c+d*x]^p*(a*Sin[c+d*x]+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,p},x] && IntegerQ[n]


(* ::Subsection::Closed:: *)
(*8 trig^m (a+b tan^n)^p*)


Int[1/(a_+b_.*tan[c_.+d_.*x_]^2),x_Symbol] :=
  1/a*Int[Cos[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b]


Int[1/(a_+b_.*cot[c_.+d_.*x_]^2),x_Symbol] :=
  1/a*Int[Sin[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b]


Int[1/(a_+b_.*tan[c_.+d_.*x_]^2),x_Symbol] :=
  x/(a-b) - b/(a-b)*Int[Sec[c+d*x]^2/(a+b*Tan[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b]


Int[1/(a_+b_.*cot[c_.+d_.*x_]^2),x_Symbol] :=
  x/(a-b) - b/(a-b)*Int[Csc[c+d*x]^2/(a+b*Cot[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b]


Int[(a_+b_.*tan[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  e/d*Subst[Int[(a+b*e^2*x^2)^p/(1+e^2*x^2),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[p+1]


Int[(a_+b_.*cot[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Module[{e=FreeFactors[Cot[c+d*x],x]},
  -e/d*Subst[Int[(a+b*e^2*x^2)^p/(1+e^2*x^2),x],x,Cot[c+d*x]/e]] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[p+1]


Int[(a_+b_.*tan[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  1/d*Subst[Int[(a+b*x^n)^p/(1+x^2),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_+b_.*cot[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  -1/d*Subst[Int[(a+b*x^n)^p/(1+x^2),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d,n,p},x]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*(e_.*tan[c_.+d_.*x_])^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f^(m+1)/d*Subst[Int[x^m*(a+b*(e*f*x)^n)^p/(1+f^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && IntegerQ[m/2]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*(e_.*cot[c_.+d_.*x_])^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f^(m+1)/d*Subst[Int[x^m*(a+b*(e*f*x)^n)^p/(1+f^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && IntegerQ[m/2]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*ExpandToSum[a*(f*x)^n+b*(1-f^2*x^2)^(n/2),x]^p/(f*x)^(n*p),x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*ExpandToSum[a*(f*x)^n+b*(1-f^2*x^2)^(n/2),x]^p/(f*x)^(n*p),x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*(e_.*tan[c_.+d_.*x_])^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f/d*Subst[Int[(a+b*(e*f*x)^n)^p/(1+f^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && EvenQ[m]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*(e_.*cot[c_.+d_.*x_])^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f/d*Subst[Int[(a+b*(e*f*x)^n)^p/(1+f^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && EvenQ[m]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f/d*Subst[Int[(1-f^2*x^2)^((m-n*p-1)/2)*ExpandToSum[b*(f*x)^n+a*(1-f^2*x^2)^(n/2),x]^p,x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f/d*Subst[Int[(1-f^2*x^2)^((m-n*p-1)/2)*ExpandToSum[b*(f*x)^n+a*(1-f^2*x^2)^(n/2),x]^p,x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[tan[c_.+d_.*x_]^m_.*(a_+b_.*(e_.*tan[c_.+d_.*x_])^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f/d*Subst[Int[(f*x)^m*(a+b*(e*f*x)^n)^p/(1+f^2*x^2),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*(e_.*cot[c_.+d_.*x_])^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f/d*Subst[Int[(f*x)^m*(a+b*(e*f*x)^n)^p/(1+f^2*x^2),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


(* ::Subsection::Closed:: *)
(*9 trig^m (a+b tan^n+c tan^(2 n))^p*)


Int[(a_+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Tan[d+e*x]^n+c*Tan[d+e*x]^(2*n))^p/(b+2*c*Tan[d+e*x]^n)^(2*p)*Int[(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cot[d+e*x]^n+c*Cot[d+e*x]^(2*n))^p/(b+2*c*Cot[d+e*x]^n)^(2*p)*Int[(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[1/(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Tan[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Tan[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[1/(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Cot[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Cot[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*(f_.*tan[d_.+e_.*x_])^n_.+c_.*(f_.*tan[d_.+e_.*x_])^n2_.)^p_,x_Symbol] :=
  Module[{g=FreeFactors[Tan[d+e*x],x]},
  g^(m+1)/e*Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2)^(m/2+1),x],x,Tan[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && IntegerQ[m/2]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*(f_.*cot[d_.+e_.*x_])^n_.+c_.*(f_.*cot[d_.+e_.*x_])^n2_.)^p_,x_Symbol] :=
  Module[{g=FreeFactors[Cot[d+e*x],x]},
  -g^(m+1)/e*Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2)^(m/2+1),x],x,Cot[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && IntegerQ[m/2]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*ExpandToSum[a*(g*x)^(2*n)+b*(g*x)^n*(1-g^2*x^2)^(n/2)+c*(1-g^2*x^2)^n,x]^p/(g*x)^(2*n*p),x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*ExpandToSum[a*(g*x)^(2*n)+b*(g*x)^n*(1-g^2*x^2)^(n/2)+c*(1-g^2*x^2)^n,x]^p/(g*x)^(2*n*p),x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*(f_.*tan[d_.+e_.*x_])^n_.+c_.*(f_.*tan[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Tan[d+e*x],x]},
  g/e*Subst[Int[(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2)^(m/2+1),x],x,Tan[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && EvenQ[m]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*(f_.*cot[d_.+e_.*x_])^n_.+c_.*(f_.*cot[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cot[d+e*x],x]},
  -g/e*Subst[Int[(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2)^(m/2+1),x],x,Cot[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && EvenQ[m]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g/e*Subst[Int[(1-g^2*x^2)^((m-2*n*p-1)/2)*ExpandToSum[c*x^(2*n)+b*x^n*(1-x^2)^(n/2)+a*(1-x^2)^n,x]^p,x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g/e*Subst[Int[(1-g^2*x^2)^((m-2*n*p-1)/2)*ExpandToSum[c*x^(2*n)+b*x^n*(1-x^2)^(n/2)+a*(1-x^2)^n,x]^p,x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Tan[d+e*x]^m*(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Cot[d+e*x]^m*(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Tan[d+e*x]^n+c*Tan[d+e*x]^(2*n))^p/(b+2*c*Tan[d+e*x]^n)^(2*p)*Int[Tan[d+e*x]^m*(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cot[d+e*x]^n+c*Cot[d+e*x]^(2*n))^p/(b+2*c*Cot[d+e*x]^n)^(2*p)*Int[Cot[d+e*x]^m*(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*tan[d_.+e_.*x_])^n_.+c_.*(f_.*tan[d_.+e_.*x_])^n2_.)^p_,x_Symbol] :=
  Module[{g=FreeFactors[Tan[d+e*x],x]},
  g/e*Subst[Int[(g*x)^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2),x],x,Tan[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*cot[d_.+e_.*x_])^n_.+c_.*(f_.*cot[d_.+e_.*x_])^n2_.)^p_,x_Symbol] :=
  Module[{g=FreeFactors[Cot[d+e*x],x]},
  -g/e*Subst[Int[(g*x)^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2),x],x,Cot[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Cot[d+e*x]^m*(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Tan[d+e*x]^m*(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Tan[d+e*x]^n+c*Tan[d+e*x]^(2*n))^p/(b+2*c*Tan[d+e*x]^n)^(2*p)*Int[Cot[d+e*x]^m*(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cot[d+e*x]^n+c*Cot[d+e*x]^(2*n))^p/(b+2*c*Cot[d+e*x]^n)^(2*p)*Int[Tan[d+e*x]^m*(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_+c_.*tan[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cot[d+e*x],x]},
  g/e*Subst[Int[(g*x)^(m-2*n*p)*(c+b*(g*x)^n+a*(g*x)^(2*n))^p/(1+g^2*x^2),x],x,Cot[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && EvenQ[n]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_+c_.*cot[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Tan[d+e*x],x]},
  -g/e*Subst[Int[(g*x)^(m-2*n*p)*(c+b*(g*x)^n+a*(g*x)^(2*n))^p/(1+g^2*x^2),x],x,Tan[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && EvenQ[n]


Int[(A_+B_.*tan[d_.+e_.*x_])*(a_+b_.*tan[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Tan[d+e*x])*(b+2*c*Tan[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*cot[d_.+e_.*x_])*(a_+b_.*cot[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Cot[d+e*x])*(b+2*c*Cot[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*tan[d_.+e_.*x_])*(a_+b_.*tan[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Tan[d+e*x]+c*Tan[d+e*x]^2)^n/(b+2*c*Tan[d+e*x])^(2*n)*Int[(A+B*Tan[d+e*x])*(b+2*c*Tan[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*cot[d_.+e_.*x_])*(a_+b_.*cot[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Cot[d+e*x]+c*Cot[d+e*x]^2)^n/(b+2*c*Cot[d+e*x])^(2*n)*Int[(A+B*Cot[d+e*x])*(b+2*c*Cot[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*tan[d_.+e_.*x_])/(a_.+b_.*tan[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/Simp[b+q+2*c*Tan[d+e*x],x],x] + 
  (B-(b*B-2*A*c)/q)*Int[1/Simp[b-q+2*c*Tan[d+e*x],x],x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*cot[d_.+e_.*x_])/(a_.+b_.*cot[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/Simp[b+q+2*c*Cot[d+e*x],x],x] + 
  (B-(b*B-2*A*c)/q)*Int[1/Simp[b-q+2*c*Cot[d+e*x],x],x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*tan[d_.+e_.*x_])*(a_.+b_.*tan[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*tan[d+e*x])*(a+b*tan[d+e*x]+c*tan[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*cot[d_.+e_.*x_])*(a_.+b_.*cot[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*cot[d+e*x])*(a+b*cot[d+e*x]+c*cot[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c] && IntegerQ[n]


(* ::Subsection::Closed:: *)
(*10 Tangent normalization rules*)


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Tan[a+b*x])^m*Int[ActivateTrig[u]*(d*Tan[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m*Int[ActivateTrig[u]*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(c*Tan[a+b*x])^m*Int[ActivateTrig[u]/(c*Tan[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownTangentIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(c*Tan[a+b*x])^m*Int[ActivateTrig[u]/(c*Cot[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownCotangentIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^n_.*(A_+B_.*cot[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-1)*(B+A*Tan[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(c_.*cot[a_.+b_.*x_])^n_.*(A_+B_.*tan[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-1)*(B+A*Cot[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(A_+B_.*cot[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Tan[a+b*x])/Tan[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(A_+B_.*tan[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Cot[a+b*x])/Cot[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownCotangentIntegrandQ[u,x]


Int[u_.*(c_.*tan[a_.+b_.*x_])^n_.*(A_.+B_.*cot[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-2)*(C+B*Tan[a+b*x]+A*Tan[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownTangentIntegrandQ[u,x]


Int[u_.*(c_.*cot[a_.+b_.*x_])^n_.*(A_.+B_.*tan[a_.+b_.*x_]+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-2)*(C+B*Cot[a+b*x]+A*Cot[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownCotangentIntegrandQ[u,x]


Int[u_.*(c_.*tan[a_.+b_.*x_])^n_.*(A_+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-2)*(C+A*Tan[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownTangentIntegrandQ[u,x]


Int[u_.*(c_.*cot[a_.+b_.*x_])^n_.*(A_+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-2)*(C+A*Cot[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(A_.+B_.*cot[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Tan[a+b*x]+A*Tan[a+b*x]^2)/Tan[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(A_.+B_.*tan[a_.+b_.*x_]+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Cot[a+b*x]+A*Cot[a+b*x]^2)/Cot[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(A_+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Tan[a+b*x]^2)/Tan[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(A_+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Cot[a+b*x]^2)/Cot[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(A_.+B_.*tan[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Tan[a+b*x]+B*Tan[a+b*x]^2)/Tan[a+b*x],x] /;
FreeQ[{a,b,A,B,C},x]


Int[u_*(A_.*tan[a_.+b_.*x_]^n_.+B_.*tan[a_.+b_.*x_]^n1_+C_.*tan[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Tan[a+b*x]^n*(A+B*Tan[a+b*x]+C*Tan[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && ZeroQ[n1-n-1] && ZeroQ[n2-n-2]


Int[u_*(A_.*cot[a_.+b_.*x_]^n_.+B_.*cot[a_.+b_.*x_]^n1_+C_.*cot[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Cot[a+b*x]^n*(A+B*Cot[a+b*x]+C*Cot[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && ZeroQ[n1-n-1] && ZeroQ[n2-n-2]
