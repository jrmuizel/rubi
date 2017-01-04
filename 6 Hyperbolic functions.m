(* ::Package:: *)

(* ::Section:: *)
(*Hyperbolic Function Rules*)


(* ::Subsection::Closed:: *)
(*1.10 (c+d x)^m (a+b sinh)^n*)


Int[(c_.+d_.*x_)^m_.*Sinh[e_.+f_.*x_],x_Symbol] :=
  (c+d*x)^m*Cosh[e+f*x]/f - 
  d*m/f*Int[(c+d*x)^(m-1)*Cosh[e+f*x],x] /;
FreeQ[{c,d,e,f},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Cosh[e_.+f_.*x_],x_Symbol] :=
  (c+d*x)^m*Sinh[e+f*x]/f - 
  d*m/f*Int[(c+d*x)^(m-1)*Sinh[e+f*x],x] /;
FreeQ[{c,d,e,f},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_*Sinh[e_.+f_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Sinh[e+f*x]/(d*(m+1)) -
  f/(d*(m+1))*Int[(c+d*x)^(m+1)*Cosh[e+f*x],x] /;
FreeQ[{c,d,e,f},x] && RationalQ[m] && m<-1


Int[(c_.+d_.*x_)^m_*Cosh[e_.+f_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Cosh[e+f*x]/(d*(m+1)) -
  f/(d*(m+1))*Int[(c+d*x)^(m+1)*Sinh[e+f*x],x] /;
FreeQ[{c,d,e,f},x] && RationalQ[m] && m<-1


Int[Sinh[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  SinhIntegral[e+f*x]/d /;
FreeQ[{c,d,e,f},x] && ZeroQ[d*e-c*f]


Int[Cosh[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  CoshIntegral[e+f*x]/d /;
FreeQ[{c,d,e,f},x] && ZeroQ[d*e-c*f]


Int[Sinh[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Cosh[(d*e-c*f)/d]*Int[Sinh[c*f/d+f*x]/(c+d*x),x] + 
  Sinh[(d*e-c*f)/d]*Int[Cosh[c*f/d+f*x]/(c+d*x),x] /;
FreeQ[{c,d,e,f},x] && NonzeroQ[d*e-c*f]


Int[Cosh[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Cosh[(d*e-c*f)/d]*Int[Cosh[c*f/d+f*x]/(c+d*x),x] + 
  Sinh[(d*e-c*f)/d]*Int[Sinh[c*f/d+f*x]/(c+d*x),x] /;
FreeQ[{c,d,e,f},x] && NonzeroQ[d*e-c*f]


Int[(c_.+d_.*x_)^m_.*Sinh[e_.+f_.*x_],x_Symbol] :=
  1/2*Int[(c+d*x)^m*E^(e+f*x),x] - 1/2*Int[(c+d*x)^m*E^(-(e+f*x)),x] /;
FreeQ[{c,d,e,f,m},x]


Int[(c_.+d_.*x_)^m_.*Cosh[e_.+f_.*x_],x_Symbol] :=
  1/2*Int[(c+d*x)^m*E^(e+f*x),x] + 1/2*Int[(c+d*x)^m*E^(-(e+f*x)),x] /;
FreeQ[{c,d,e,f,m},x]


Int[(c_.+d_.*x_)*(b_.*Sinh[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*(b*Sinh[e+f*x])^n/(f^2*n^2) + 
  b*(c+d*x)*Cosh[e+f*x]*(b*Sinh[e+f*x])^(n-1)/(f*n) - 
  b^2*(n-1)/n*Int[(c+d*x)*(b*Sinh[e+f*x])^(n-2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[n] && n>1


Int[(c_.+d_.*x_)*(b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*(b*Cosh[e+f*x])^n/(f^2*n^2) + 
  b*(c+d*x)*Sinh[e+f*x]*(b*Cosh[e+f*x])^(n-1)/(f*n) + 
  b^2*(n-1)/n*Int[(c+d*x)*(b*Cosh[e+f*x])^(n-2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[n] && n>1


Int[(c_.+d_.*x_)^m_*(b_.*Sinh[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*m*(c+d*x)^(m-1)*(b*Sinh[e+f*x])^n/(f^2*n^2) + 
  b*(c+d*x)^m*Cosh[e+f*x]*(b*Sinh[e+f*x])^(n-1)/(f*n) - 
  b^2*(n-1)/n*Int[(c+d*x)^m*(b*Sinh[e+f*x])^(n-2),x] + 
  d^2*m*(m-1)/(f^2*n^2)*Int[(c+d*x)^(m-2)*(b*Sinh[e+f*x])^n,x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n>1 && m>1


Int[(c_.+d_.*x_)^m_*(b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*m*(c+d*x)^(m-1)*(b*Cosh[e+f*x])^n/(f^2*n^2) + 
  b*(c+d*x)^m*Sinh[e+f*x]*(b*Cosh[e+f*x])^(n-1)/(f*n) + 
  b^2*(n-1)/n*Int[(c+d*x)^m*(b*Cosh[e+f*x])^(n-2),x] + 
  d^2*m*(m-1)/(f^2*n^2)*Int[(c+d*x)^(m-2)*(b*Cosh[e+f*x])^n,x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n>1 && m>1


Int[(c_.+d_.*x_)^m_*Sinh[e_.+f_.*x_]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Sinh[e+f*x]^n,x],x] /;
FreeQ[{c,d,e,f,m},x] && IntegerQ[n] && n>1 && (Not[RationalQ[m]] || -1<=m<1)


Int[(c_.+d_.*x_)^m_*Cosh[e_.+f_.*x_]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Cosh[e+f*x]^n,x],x] /;
FreeQ[{c,d,e,f,m},x] && IntegerQ[n] && n>1 && (Not[RationalQ[m]] || -1<=m<1)


Int[(c_.+d_.*x_)^m_*Sinh[e_.+f_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Sinh[e+f*x]^n/(d*(m+1)) - 
  f*n/(d*(m+1))*Int[ExpandTrigReduce[(c+d*x)^(m+1),Cosh[e+f*x]*Sinh[e+f*x]^(n-1),x],x] /;
FreeQ[{c,d,e,f,m},x] && IntegerQ[n] && n>1 && RationalQ[m] && -2<=m<-1


Int[(c_.+d_.*x_)^m_*Cosh[e_.+f_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Cosh[e+f*x]^n/(d*(m+1)) - 
  f*n/(d*(m+1))*Int[ExpandTrigReduce[(c+d*x)^(m+1),Sinh[e+f*x]*Cosh[e+f*x]^(n-1),x],x] /;
FreeQ[{c,d,e,f,m},x] && IntegerQ[n] && n>1 && RationalQ[m] && -2<=m<-1


Int[(c_.+d_.*x_)^m_*(b_.*Sinh[e_.+f_.*x_])^n_,x_Symbol] :=
  (c+d*x)^(m+1)*(b*Sinh[e+f*x])^n/(d*(m+1)) - 
  b*f*n*(c+d*x)^(m+2)*Cosh[e+f*x]*(b*Sinh[e+f*x])^(n-1)/(d^2*(m+1)*(m+2)) + 
  f^2*n^2/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*(b*Sinh[e+f*x])^n,x] + 
  b^2*f^2*n*(n-1)/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*(b*Sinh[e+f*x])^(n-2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n>1 && m<-2


Int[(c_.+d_.*x_)^m_*(b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  (c+d*x)^(m+1)*(b*Cosh[e+f*x])^n/(d*(m+1)) - 
  b*f*n*(c+d*x)^(m+2)*Sinh[e+f*x]*(b*Cosh[e+f*x])^(n-1)/(d^2*(m+1)*(m+2)) + 
  f^2*n^2/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*(b*Cosh[e+f*x])^n,x] - 
  b^2*f^2*n*(n-1)/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*(b*Cosh[e+f*x])^(n-2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n>1 && m<-2


Int[(c_.+d_.*x_)*(b_.*Sinh[e_.+f_.*x_])^n_,x_Symbol] :=
  (c+d*x)*Cosh[e+f*x]*(b*Sinh[e+f*x])^(n+1)/(b*f*(n+1)) - 
  d*(b*Sinh[e+f*x])^(n+2)/(b^2*f^2*(n+1)*(n+2)) - 
  (n+2)/(b^2*(n+1))*Int[(c+d*x)*(b*Sinh[e+f*x])^(n+2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[n] && n<-1 && n!=-2


Int[(c_.+d_.*x_)*(b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  -(c+d*x)*Sinh[e+f*x]*(b*Cosh[e+f*x])^(n+1)/(b*f*(n+1)) + 
  d*(b*Cosh[e+f*x])^(n+2)/(b^2*f^2*(n+1)*(n+2)) + 
  (n+2)/(b^2*(n+1))*Int[(c+d*x)*(b*Cosh[e+f*x])^(n+2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[n] && n<-1 && n!=-2


Int[(c_.+d_.*x_)^m_.*(b_.*Sinh[e_.+f_.*x_])^n_,x_Symbol] :=
  (c+d*x)^m*Cosh[e+f*x]*(b*Sinh[e+f*x])^(n+1)/(b*f*(n+1)) - 
  d*m*(c+d*x)^(m-1)*(b*Sinh[e+f*x])^(n+2)/(b^2*f^2*(n+1)*(n+2)) - 
  (n+2)/(b^2*(n+1))*Int[(c+d*x)^m*(b*Sinh[e+f*x])^(n+2),x] + 
  d^2*m*(m-1)/(b^2*f^2*(n+1)*(n+2))*Int[(c+d*x)^(m-2)*(b*Sinh[e+f*x])^(n+2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n<-1 && n!=-2 && m>1


Int[(c_.+d_.*x_)^m_.*(b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  -(c+d*x)^m*Sinh[e+f*x]*(b*Cosh[e+f*x])^(n+1)/(b*f*(n+1)) + 
  d*m*(c+d*x)^(m-1)*(b*Cosh[e+f*x])^(n+2)/(b^2*f^2*(n+1)*(n+2)) + 
  (n+2)/(b^2*(n+1))*Int[(c+d*x)^m*(b*Cosh[e+f*x])^(n+2),x] - 
  d^2*m*(m-1)/(b^2*f^2*(n+1)*(n+2))*Int[(c+d*x)^(m-2)*(b*Cosh[e+f*x])^(n+2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n<-1 && n!=-2 && m>1


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Sinh[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*Sinh[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[n] && (n==1 || PositiveIntegerQ[m] || NonzeroQ[a^2+b^2])


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Cosh[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*Cosh[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[n] && (n==1 || PositiveIntegerQ[m] || NonzeroQ[a^2-b^2])


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Sinh[e_.+f_.*x_])^n_.,x_Symbol] :=
  (2*a)^n*Int[(c+d*x)^m*Cosh[-Pi*a/(4*b)+e/2+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2+b^2] && IntegerQ[n]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Sinh[e_.+f_.*x_])^n_,x_Symbol] :=
  (2*a)^IntPart[n]*(a+b*Sinh[e+f*x])^FracPart[n]/Cosh[-Pi*a/(4*b)+e/2+f*x/2]^(2*FracPart[n])*
    Int[(c+d*x)^m*Cosh[-Pi*a/(4*b)+e/2+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2+b^2] && IntegerQ[2*n] && (n>0 || PositiveIntegerQ[m])


(* Int[(c_.+d_.*x_)^m_.*(a_+b_.*Cosh[e_.+f_.*x_])^n_.,x_Symbol] :=
  (2*a)^n*Int[(c+d*x)^m*Cosh[-Pi/4*(1-a/b)+e/2+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && IntegerQ[n] *)


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Cosh[e_.+f_.*x_])^n_.,x_Symbol] :=
  (2*a)^n*Int[(c+d*x)^m*Cosh[e/2+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a-b] && IntegerQ[n]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Cosh[e_.+f_.*x_])^n_.,x_Symbol] :=
  (-2*a)^n*Int[(c+d*x)^m*Sinh[e/2+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a+b] && IntegerQ[n]


(* Int[(c_.+d_.*x_)^m_.*(a_+b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  (2*a)^(n-1/2)*Sqrt[a+b*Cosh[e+f*x]]/Cosh[-Pi/4*(1-a/b)+e/2+f*x/2]*Int[(c+d*x)^m*Cosh[-Pi/4*(1-a/b)+e/2+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[n]] *)


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  (2*a)^IntPart[n]*(a+b*Cosh[e+f*x])^FracPart[n]/Cosh[e/2+f*x/2]^(2*FracPart[n])*Int[(c+d*x)^m*Cosh[e/2+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a-b] && IntegerQ[2*n] && (n>0 || PositiveIntegerQ[m])


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  (-2*a)^IntPart[n]*(a+b*Cosh[e+f*x])^FracPart[n]/Sinh[e/2+f*x/2]^(2*FracPart[n])*Int[(c+d*x)^m*Sinh[e/2+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a+b] && IntegerQ[2*n] && (n>0 || PositiveIntegerQ[m])


Int[(c_.+d_.*x_)^m_./(a_+b_.*Sinh[e_.+f_.*x_]),x_Symbol] :=
  -2*Int[(c+d*x)^m*E^(e+f*x)/(b-2*a*E^(e+f*x)-b*E^(2*(e+f*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2+b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_./(a_+b_.*Cosh[e_.+f_.*x_]),x_Symbol] :=
  2*Int[(c+d*x)^m*E^(e+f*x)/(b+2*a*E^(e+f*x)+b*E^(2*(e+f*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_./(a_+b_.*Sinh[e_.+f_.*x_])^2,x_Symbol] :=
  -b*(c+d*x)^m*Cosh[e+f*x]/(f*(a^2+b^2)*(a+b*Sinh[e+f*x])) + 
  a/(a^2+b^2)*Int[(c+d*x)^m/(a+b*Sinh[e+f*x]),x] + 
  b*d*m/(f*(a^2+b^2))*Int[(c+d*x)^(m-1)*Cosh[e+f*x]/(a+b*Sinh[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2+b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_./(a_+b_.*Cosh[e_.+f_.*x_])^2,x_Symbol] :=
  -b*(c+d*x)^m*Sinh[e+f*x]/(f*(a^2-b^2)*(a+b*Cosh[e+f*x])) + 
  a/(a^2-b^2)*Int[(c+d*x)^m/(a+b*Cosh[e+f*x]),x] + 
  b*d*m/(f*(a^2-b^2))*Int[(c+d*x)^(m-1)*Sinh[e+f*x]/(a+b*Cosh[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Sinh[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(c+d*x)^m*Cosh[e+f*x]*(a+b*Sinh[e+f*x])^(n+1)/(f*(n+1)*(a^2+b^2)) + 
  a/(a^2+b^2)*Int[(c+d*x)^m*(a+b*Sinh[e+f*x])^(n+1),x] - 
  b*d*m/(f*(n+1)*(a^2+b^2))*Int[(c+d*x)^(m-1)*Cosh[e+f*x]*(a+b*Sinh[e+f*x])^(n+1),x] - 
  b*(n+2)/((n+1)*(a^2+b^2))*Int[(c+d*x)^m*Sinh[e+f*x]*(a+b*Sinh[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2+b^2] && NegativeIntegerQ[n+2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Cosh[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(c+d*x)^m*Sinh[e+f*x]*(a+b*Cosh[e+f*x])^(n+1)/(f*(n+1)*(a^2-b^2)) + 
  a/(a^2-b^2)*Int[(c+d*x)^m*(a+b*Cosh[e+f*x])^(n+1),x] - 
  b*d*m/(f*(n+1)*(a^2-b^2))*Int[(c+d*x)^(m-1)*Sinh[e+f*x]*(a+b*Cosh[e+f*x])^(n+1),x] - 
  b*(n+2)/((n+1)*(a^2-b^2))*Int[(c+d*x)^m*Cosh[e+f*x]*(a+b*Cosh[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NegativeIntegerQ[n+2] && PositiveIntegerQ[m]


Int[u_^m_.*(a_.+b_.*Sinh[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Sinh[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*(a_.+b_.*Cosh[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Cosh[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*Sinh[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(c+d*x)^m*(a+b*Sinh[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*Cosh[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(c+d*x)^m*(a+b*Cosh[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]





(* ::Subsection::Closed:: *)
(*1.11 (e x)^m (a+b x^n)^p sinh*)


Int[(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sinh[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[p]


Int[(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cosh[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[p]


Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  x^(-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) - 
  (-n+1)/(b*n*(p+1))*Int[x^(-n)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && PositiveIntegerQ[n] && p<-1 && n>2


Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  x^(-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) - 
  (-n+1)/(b*n*(p+1))*Int[x^(-n)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && PositiveIntegerQ[n] && p<-1 && n>2


Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sinh[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && PositiveIntegerQ[n] && (n==2 || p==-1)


Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cosh[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && PositiveIntegerQ[n] && (n==2 || p==-1)


Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[x^(n*p)*(b+a*x^(-n))^p*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[x^(n*p)*(b+a*x^(-n))^p*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Defer[Int][(a+b*x^n)^p*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Defer[Int][(a+b*x^n)^p*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sinh[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cosh[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  e^m*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) - 
  d*e^m/(b*n*(p+1))*Int[(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && ZeroQ[m-n+1] && RationalQ[p] && p<-1 && (IntegerQ[n] || PositiveQ[e])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  e^m*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) - 
  d*e^m/(b*n*(p+1))*Int[(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && ZeroQ[m-n+1] && RationalQ[p] && p<-1 && (IntegerQ[n] || PositiveQ[e])


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  x^(m-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && PositiveIntegerQ[n] && RationalQ[m] && p<-1 && (m-n+1>0 || n>2)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  x^(m-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && PositiveIntegerQ[n] && RationalQ[m] && p<-1 && (m-n+1>0 || n>2)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sinh[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && IntegerQ[m] && PositiveIntegerQ[n] && (n==2 || p==-1)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cosh[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && IntegerQ[m] && PositiveIntegerQ[n] && (n==2 || p==-1)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[x^(m+n*p)*(b+a*x^(-n))^p*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,m},x] && NegativeIntegerQ[p] && NegativeIntegerQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[x^(m+n*p)*(b+a*x^(-n))^p*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,m},x] && NegativeIntegerQ[p] && NegativeIntegerQ[n]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
  Defer[Int][(e*x)^m*(a+b*x^n)^p*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
  Defer[Int][(e*x)^m*(a+b*x^n)^p*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]





(* ::Subsection::Closed:: *)
(*1.12 (e x)^m (a+b sinh(c+d x^n))^p*)


Int[Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(c+d*x^n),x] - 1/2*Int[E^(-c-d*x^n),x] /;
FreeQ[{c,d},x] && IntegerQ[n] && n>1


Int[Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(c+d*x^n),x] + 1/2*Int[E^(-c-d*x^n),x] /;
FreeQ[{c,d},x] && IntegerQ[n] && n>1


Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Sinh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && n>1 && p>1


Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Cosh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && n>1 && p>1


Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NegativeIntegerQ[n]


Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NegativeIntegerQ[n]


Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*Sinh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && FractionQ[n]


Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*Cosh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && FractionQ[n]


Int[Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(c+d*x^n),x] - 1/2*Int[E^(-c-d*x^n),x] /;
FreeQ[{c,d,n},x]


Int[Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(c+d*x^n),x] + 1/2*Int[E^(-c-d*x^n),x] /;
FreeQ[{c,d,n},x]


Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Sinh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[p]


Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Cosh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[p]


Int[(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Sinh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[p] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Cosh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[p] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_,x_Symbol] :=
  Defer[Int][(a+b*Sinh[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x]


Int[(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_,x_Symbol] :=
  Defer[Int][(a+b*Cosh[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x]


Int[(a_.+b_.*Sinh[u_])^p_.,x_Symbol] :=
  Int[(a+b*Sinh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*Cosh[u_])^p_.,x_Symbol] :=
  Int[(a+b*Cosh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[Sinh[d_.*x_^n_]/x_,x_Symbol] :=
  SinhIntegral[d*x^n]/n /;
FreeQ[{d,n},x]


Int[Cosh[d_.*x_^n_]/x_,x_Symbol] :=
  CoshIntegral[d*x^n]/n /;
FreeQ[{d,n},x]


Int[Sinh[c_+d_.*x_^n_]/x_,x_Symbol] :=
  Sinh[c]*Int[Cosh[d*x^n]/x,x] + Cosh[c]*Int[Sinh[d*x^n]/x,x] /;
FreeQ[{c,d,n},x]


Int[Cosh[c_+d_.*x_^n_]/x_,x_Symbol] :=
  Cosh[c]*Int[Cosh[d*x^n]/x,x] + Sinh[c]*Int[Sinh[d*x^n]/x,x] /;
FreeQ[{c,d,n},x]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{mn=Simplify[(m+1)/n]},
  1/n*Subst[Int[x^(mn-1)*(a+b*Sinh[c+d*x])^p,x],x,x^n] /;
 IntegerQ[mn] && (p==1 || mn>0)] /;
FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{mn=Simplify[(m+1)/n]},
  1/n*Subst[Int[x^(mn-1)*(a+b*Cosh[c+d*x])^p,x],x,x^n] /;
 IntegerQ[mn] && (p==1 || mn>0)] /;
FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p]


Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{mn=Simplify[(m+1)/n]},
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
 IntegerQ[mn] && (p==1 || mn>0)] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p]


Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{mn=Simplify[(m+1)/n]},
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
 IntegerQ[mn] && (p==1 || mn>0)] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p]


Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*Cosh[c+d*x^n]/(d*n) - 
  e^n*(m-n+1)/(d*n)*Int[(e*x)^(m-n)*Cosh[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && PositiveIntegerQ[n] && RationalQ[m] && 0<n<m+1


Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*Sinh[c+d*x^n]/(d*n) - 
  e^n*(m-n+1)/(d*n)*Int[(e*x)^(m-n)*Sinh[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && PositiveIntegerQ[n] && RationalQ[m] && 0<n<m+1


Int[(e_.*x_)^m_*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  (e*x)^(m+1)*Sinh[c+d*x^n]/(e*(m+1)) - 
  d*n/(e^n*(m+1))*Int[(e*x)^(m+n)*Cosh[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[(e_.*x_)^m_*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  (e*x)^(m+1)*Cosh[c+d*x^n]/(e*(m+1)) - 
  d*n/(e^n*(m+1))*Int[(e*x)^(m+n)*Sinh[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(c+d*x^n),x] - 1/2*Int[(e*x)^m*E^(-c-d*x^n),x] /;
FreeQ[{c,d,e,m},x] && PositiveIntegerQ[n]


Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(c+d*x^n),x] + 1/2*Int[(e*x)^m*E^(-c-d*x^n),x] /;
FreeQ[{c,d,e,m},x] && PositiveIntegerQ[n]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -Sinh[a+b*x^n]^p/((n-1)*x^(n-1)) + 
  b*n*p/(n-1)*Int[Sinh[a+b*x^n]^(p-1)*Cosh[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && ZeroQ[m+n] && p>1 && NonzeroQ[n-1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -Cosh[a+b*x^n]^p/((n-1)*x^(n-1)) + 
  b*n*p/(n-1)*Int[Cosh[a+b*x^n]^(p-1)*Sinh[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && ZeroQ[m+n] && p>1 && NonzeroQ[n-1]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -n*Sinh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^n*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/(b*n*p) -
  (p-1)/p*Int[x^m*Sinh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-2*n+1] && RationalQ[p] && p>1


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -n*Cosh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^n*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Cosh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-2*n+1] && RationalQ[p] && p>1


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -(m-n+1)*x^(m-2*n+1)*Sinh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^(m-n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/(b*n*p) -
  (p-1)/p*Int[x^m*Sinh[a+b*x^n]^(p-2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2)*Int[x^(m-2*n)*Sinh[a+b*x^n]^p,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<m+1


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -(m-n+1)*x^(m-2*n+1)*Cosh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^(m-n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Cosh[a+b*x^n]^(p-2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2)*Int[x^(m-2*n)*Cosh[a+b*x^n]^p,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<m+1


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m+1)*Sinh[a+b*x^n]^p/(m+1) - 
  b*n*p*x^(m+n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) + 
  b^2*n^2*p^2/((m+1)*(m+n+1))*Int[x^(m+2*n)*Sinh[a+b*x^n]^p,x] + 
  b^2*n^2*p*(p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*Sinh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<1-m && NonzeroQ[m+n+1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m+1)*Cosh[a+b*x^n]^p/(m+1) - 
  b*n*p*x^(m+n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) + 
  b^2*n^2*p^2/((m+1)*(m+n+1))*Int[x^(m+2*n)*Cosh[a+b*x^n]^p,x] - 
  b^2*n^2*p*(p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*Cosh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<1-m && NonzeroQ[m+n+1]


Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  k/e*Subst[Int[x^(k*(m+1)-1)*(a+b*Sinh[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  k/e*Subst[Int[x^(k*(m+1)-1)*(a+b*Cosh[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Sinh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && p>1


Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Cosh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && p>1


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^n*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  n*Sinh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) - 
  (p+2)/(p+1)*Int[x^m*Sinh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-2*n+1] && RationalQ[p] && p<-1 && p!=-2


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^n*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) + 
  n*Cosh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) + 
  (p+2)/(p+1)*Int[x^m*Cosh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-2*n+1] && RationalQ[p] && p<-1 && p!=-2


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m-n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)*x^(m-2*n+1)*Sinh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) -
  (p+2)/(p+1)*Int[x^m*Sinh[a+b*x^n]^(p+2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2))*Int[x^(m-2*n)*Sinh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p<-1 && p!=-2 && 0<2*n<m+1 


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^(m-n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) +
  (m-n+1)*x^(m-2*n+1)*Cosh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (p+2)/(p+1)*Int[x^m*Cosh[a+b*x^n]^(p+2),x] -
  (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2))*Int[x^(m-2*n)*Cosh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p<-1 && p!=-2 && 0<2*n<m+1 


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NegativeIntegerQ[n] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/e*Subst[Int[(a+b*Sinh[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && NegativeIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/e*Subst[Int[(a+b*Cosh[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && NegativeIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*Sinh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*Cosh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]


Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]


Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*Sinh[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*Cosh[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(c+d*x^n),x] - 1/2*Int[(e*x)^m*E^(-c-d*x^n),x] /;
FreeQ[{c,d,e,m,n},x]


Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(c+d*x^n),x] + 1/2*Int[(e*x)^m*E^(-c-d*x^n),x] /;
FreeQ[{c,d,e,m,n},x]


Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Sinh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Cosh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*(a+b*Sinh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*(a+b*Cosh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x] && IntegerQ[m]


Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  Defer[Int][(e*x)^m*(a+b*Sinh[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && LinearQ[u,x]


Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  Defer[Int][(e*x)^m*(a+b*Cosh[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && LinearQ[u,x]


Int[(e_*x_)^m_.*(a_.+b_.*Sinh[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Sinh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(e_*x_)^m_.*(a_.+b_.*Cosh[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Cosh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
  Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-n+1] && NonzeroQ[p+1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
  Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-n+1] && NonzeroQ[p+1]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
  x^(m-n+1)*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Sinh[a+b*x^n]^(p+1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m,n] && 0<n<m+1 && NonzeroQ[p+1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
  x^(m-n+1)*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Cosh[a+b*x^n]^(p+1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m,n] && 0<n<m+1 && NonzeroQ[p+1]





(* ::Subsection::Closed:: *)
(*1.13 (d+e x)^m sinh(a+b x+c x^2)^n*)
(**)


Int[Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  1/2*Int[E^(a+b*x+c*x^2),x] - 1/2*Int[E^(-a-b*x-c*x^2),x] /;
FreeQ[{a,b,c},x]


Int[Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  1/2*Int[E^(a+b*x+c*x^2),x] + 1/2*Int[E^(-a-b*x-c*x^2),x] /;
FreeQ[{a,b,c},x]


Int[Sinh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[Sinh[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[Cosh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[Cosh[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[Sinh[v_]^n_.,x_Symbol] :=
  Int[Sinh[ExpandToSum[v,x]]^n,x] /;
PositiveIntegerQ[n] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[Cosh[v_]^n_.,x_Symbol] :=
  Int[Cosh[ExpandToSum[v,x]]^n,x] /;
PositiveIntegerQ[n] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[(d_.+e_.*x_)*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Cosh[a+b*x+c*x^2]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Sinh[a+b*x+c*x^2]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Cosh[a+b*x+c*x^2]/(2*c) -
  (b*e-2*c*d)/(2*c)*Int[Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Sinh[a+b*x+c*x^2]/(2*c) - 
  (b*e-2*c*d)/(2*c)*Int[Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2]/(2*c) -
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2]/(2*c) - 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2]/(2*c) -
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2],x] -
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2]/(2*c) - 
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2],x] - 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sinh[a+b*x+c*x^2]/(e*(m+1)) -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Cosh[a+b*x+c*x^2]/(e*(m+1)) - 
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sinh[a+b*x+c*x^2]/(e*(m+1)) -
  (b*e-2*c*d)/(e^2*(m+1))*Int[(d+e*x)^(m+1)*Cosh[a+b*x+c*x^2],x] -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Cosh[a+b*x+c*x^2]/(e*(m+1)) - 
  (b*e-2*c*d)/(e^2*(m+1))*Int[(d+e*x)^(m+1)*Sinh[a+b*x+c*x^2],x] -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_.*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Defer[Int][(d+e*x)^m*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x]


Int[(d_.+e_.*x_)^m_.*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Defer[Int][(d+e*x)^m*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x]


Int[(d_.+e_.*x_)^m_.*Sinh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(d+e*x)^m,Sinh[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[n] && n>1


Int[(d_.+e_.*x_)^m_.*Cosh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(d+e*x)^m,Cosh[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[n] && n>1


Int[u_^m_.*Sinh[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Sinh[ExpandToSum[v,x]]^n,x] /;
FreeQ[m,x] && PositiveIntegerQ[n] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[u_^m_.*Cosh[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Cosh[ExpandToSum[v,x]]^n,x] /;
FreeQ[m,x] && PositiveIntegerQ[n] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]





(* ::Subsection::Closed:: *)
(*2.10 (c+d x)^m (a+b tanh)^n*)


Int[(a_.+b_.*x_)^m_.*Tanh[e_.+f_.*x_],x_Symbol] :=
  -(a+b*x)^(m+1)/(b*(m+1)) + 2*Int[(a+b*x)^m*E^(2*e+2*f*x)/(1+E^(2*e+2*f*x)),x] /;
FreeQ[{a,b,e,f},x] && PositiveIntegerQ[m]


Int[(a_.+b_.*x_)^m_.*Coth[e_.+f_.*x_],x_Symbol] :=
  -(a+b*x)^(m+1)/(b*(m+1)) - 2*Int[(a+b*x)^m*E^(2*e+2*f*x)/(1-E^(2*e+2*f*x)),x] /;
FreeQ[{a,b,e,f},x] && PositiveIntegerQ[m]


Int[(a_.+b_.*x_)^m_.*(c_.*Tanh[e_.+f_.*x_])^n_,x_Symbol] :=
  -c*(a+b*x)^m*(c*Tanh[e+f*x])^(n-1)/(f*(n-1)) + 
  b*c*m/(f*(n-1))*Int[(a+b*x)^(m-1)*(c*Tanh[e+f*x])^(n-1),x] + 
  c^2*Int[(a+b*x)^m*(c*Tanh[e+f*x])^(n-2),x] /;
FreeQ[{a,b,c,e,f},x] && RationalQ[m,n] && n>1 && m>0


Int[(a_.+b_.*x_)^m_.*(c_.*Coth[e_.+f_.*x_])^n_,x_Symbol] :=
  -c*(a+b*x)^m*(c*Coth[e+f*x])^(n-1)/(f*(n-1)) + 
  b*c*m/(f*(n-1))*Int[(a+b*x)^(m-1)*(c*Coth[e+f*x])^(n-1),x] + 
  c^2*Int[(a+b*x)^m*(c*Coth[e+f*x])^(n-2),x] /;
FreeQ[{a,b,c,e,f},x] && RationalQ[m,n] && n>1 && m>0


Int[(a_.+b_.*x_)^m_.*(c_.*Tanh[e_.+f_.*x_])^n_,x_Symbol] :=
  (a+b*x)^m*(c*Tanh[e+f*x])^(n+1)/(c*f*(n+1)) - 
  b*m/(c*f*(n+1))*Int[(a+b*x)^(m-1)*(c*Tanh[e+f*x])^(n+1),x] + 
  1/c^2*Int[(a+b*x)^m*(c*Tanh[e+f*x])^(n+2),x] /;
FreeQ[{a,b,c,e,f},x] && RationalQ[m,n] && n<-1 && m>0


Int[(a_.+b_.*x_)^m_.*(c_.*Coth[e_.+f_.*x_])^n_,x_Symbol] :=
  (a+b*x)^m*(c*Coth[e+f*x])^(n+1)/(c*f*(n+1)) - 
  b*m/(c*f*(n+1))*Int[(a+b*x)^(m-1)*(c*Coth[e+f*x])^(n+1),x] + 
  1/c^2*Int[(a+b*x)^m*(c*Coth[e+f*x])^(n+2),x] /;
FreeQ[{a,b,c,e,f},x] && RationalQ[m,n] && n<-1 && m>0


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Tanh[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*Tanh[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[m,n]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Coth[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*Coth[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[m,n]


Int[(c_.+d_.*x_)^m_./(a_+b_.*Tanh[e_.+f_.*x_]),x_Symbol] :=
  (c+d*x)^(m+1)/(2*a*d*(m+1)) - 
  a*(c+d*x)^m/(2*b*f*(a+b*Tanh[e+f*x])) + 
  a*d*m/(2*b*f)*Int[(c+d*x)^(m-1)/(a+b*Tanh[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_./(a_+b_.*Coth[e_.+f_.*x_]),x_Symbol] :=
  (c+d*x)^(m+1)/(2*a*d*(m+1)) - 
  a*(c+d*x)^m/(2*b*f*(a+b*Coth[e+f*x])) + 
  a*d*m/(2*b*f)*Int[(c+d*x)^(m-1)/(a+b*Coth[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[1/((c_.+d_.*x_)^2*(a_+b_.*Tanh[e_.+f_.*x_])),x_Symbol] :=
  -1/(d*(c+d*x)*(a+b*Tanh[e+f*x])) - 
  f/(b*d)*Int[Cosh[2*e+2*f*x]/(c+d*x),x] + 
  f/(a*d)*Int[Sinh[2*e+2*f*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2]


Int[1/((c_.+d_.*x_)^2*(a_+b_.*Coth[e_.+f_.*x_])),x_Symbol] :=
  -1/(d*(c+d*x)*(a+b*Coth[e+f*x])) + 
  f/(b*d)*Int[Cosh[2*e+2*f*x]/(c+d*x),x] - 
  f/(a*d)*Int[Sinh[2*e+2*f*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2]


Int[(c_.+d_.*x_)^m_/(a_+b_.*Tanh[e_.+f_.*x_]),x_Symbol] :=
  -f*(c+d*x)^(m+2)/(b*d^2*(m+1)*(m+2)) + 
  (c+d*x)^(m+1)/(d*(m+1)*(a+b*Tanh[e+f*x])) + 
  2*b*f/(a*d*(m+1))*Int[(c+d*x)^(m+1)/(a+b*Tanh[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-2


Int[(c_.+d_.*x_)^m_/(a_+b_.*Coth[e_.+f_.*x_]),x_Symbol] :=
  -f*(c+d*x)^(m+2)/(b*d^2*(m+1)*(m+2)) + 
  (c+d*x)^(m+1)/(d*(m+1)*(a+b*Coth[e+f*x])) + 
  2*b*f/(a*d*(m+1))*Int[(c+d*x)^(m+1)/(a+b*Coth[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-2


(* Int[(c_.+d_.*x_)^m_/(a_+b_.*Tanh[e_.+f_.*x_]),x_Symbol] :=
  (c+d*x)^(m+1)/(d*(m+1)*(a+b*Tanh[e+f*x])) - 
  f/(b*d*(m+1))*Int[(c+d*x)^(m+1),x] + 
  2*b*f/(a*d*(m+1))*Int[(c+d*x)^(m+1)/(a+b*Tanh[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1 *)


(* Int[(c_.+d_.*x_)^m_/(a_+b_.*Coth[e_.+f_.*x_]),x_Symbol] :=
  (c+d*x)^(m+1)/(d*(m+1)*(a+b*Coth[e+f*x])) - 
  f/(b*d*(m+1))*Int[(c+d*x)^(m+1),x] + 
  2*b*f/(a*d*(m+1))*Int[(c+d*x)^(m+1)/(a+b*Coth[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1 *)


Int[1/((c_.+d_.*x_)*(a_+b_.*Tanh[e_.+f_.*x_])),x_Symbol] :=
  Log[c+d*x]/(2*a*d) + 
  1/(2*a)*Int[Cosh[2*e+2*f*x]/(c+d*x),x] - 
  1/(2*b)*Int[Sinh[2*e+2*f*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2]


Int[1/((c_.+d_.*x_)*(a_+b_.*Coth[e_.+f_.*x_])),x_Symbol] :=
  Log[c+d*x]/(2*a*d) - 
  1/(2*a)*Int[Cosh[2*e+2*f*x]/(c+d*x),x] + 
  1/(2*b)*Int[Sinh[2*e+2*f*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2]


Int[(c_.+d_.*x_)^m_/(a_+b_.*Tanh[e_.+f_.*x_]),x_Symbol] :=
  (c+d*x)^(m+1)/(2*a*d*(m+1)) + 
  1/(2*a)*Int[(c+d*x)^m/E^(2*a/b*(e+f*x)),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[m]]


Int[(c_.+d_.*x_)^m_/(a_+b_.*Coth[e_.+f_.*x_]),x_Symbol] :=
  (c+d*x)^(m+1)/(2*a*d*(m+1)) - 
  1/(2*a)*Int[(c+d*x)^m/E^(2*a/b*(e+f*x)),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[m]]


Int[(c_.+d_.*x_)^m_*(a_+b_.*Tanh[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(1/(2*a)+Cosh[2*e+2*f*x]/(2*a)-Sinh[2*e+2*f*x]/(2*b))^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && NegativeIntegerQ[m,n]


Int[(c_.+d_.*x_)^m_*(a_+b_.*Coth[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(1/(2*a)-Cosh[2*e+2*f*x]/(2*a)+Sinh[2*e+2*f*x]/(2*b))^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && NegativeIntegerQ[m,n]


Int[(c_.+d_.*x_)^m_*(a_+b_.*Tanh[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(1/(2*a)+1/(2*a*E^(2*a/b*(e+f*x))))^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && NegativeIntegerQ[n]


Int[(c_.+d_.*x_)^m_*(a_+b_.*Coth[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(1/(2*a)-1/(2*a*E^(2*a/b*(e+f*x))))^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && NegativeIntegerQ[n]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Tanh[e_.+f_.*x_])^n_,x_Symbol] :=
  With[{u=IntHide[(a+b*Tanh[e+f*x])^n,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[Dist[(c+d*x)^(m-1),u,x],x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && NegativeIntegerQ[n+1] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Coth[e_.+f_.*x_])^n_,x_Symbol] :=
  With[{u=IntHide[(a+b*Coth[e+f*x])^n,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[Dist[(c+d*x)^(m-1),u,x],x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[a^2-b^2] && NegativeIntegerQ[n+1] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_./(a_+b_.*Tanh[e_.+f_.*x_]),x_Symbol] :=
  (c+d*x)^(m+1)/(d*(m+1)*(a-b)) - 2*b*Int[(c+d*x)^m/(a^2-b^2+(a-b)^2*E^(-2*(e+f*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_./(a_+b_.*Coth[e_.+f_.*x_]),x_Symbol] :=
  (c+d*x)^(m+1)/(d*(m+1)*(a+b)) + 2*b*Int[(c+d*x)^m/(a^2-b^2-(a+b)^2*E^(2*(e+f*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)/(a_+b_.*Tanh[e_.+f_.*x_])^2,x_Symbol] :=
  -(c+d*x)^2/(2*d*(a^2-b^2)) + 
  b*(c+d*x)/(f*(a^2-b^2)*(a+b*Tanh[e+f*x])) - 
  1/(f*(a^2-b^2))*Int[(b*d-2*a*c*f-2*a*d*f*x)/(a+b*Tanh[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(c_.+d_.*x_)/(a_+b_.*Coth[e_.+f_.*x_])^2,x_Symbol] :=
  -(c+d*x)^2/(2*d*(a^2-b^2)) + 
  b*(c+d*x)/(f*(a^2-b^2)*(a+b*Coth[e+f*x])) - 
  1/(f*(a^2-b^2))*Int[(b*d-2*a*c*f-2*a*d*f*x)/(a+b*Coth[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Tanh[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(1/(a-b)-2*b/(a^2-b^2+(a-b)^2/E^(2*(e+f*x))))^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NegativeIntegerQ[n] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Coth[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(1/(a+b)+2*b/(a^2-b^2-(a+b)^2*E^(2*(e+f*x))))^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NegativeIntegerQ[n] && PositiveIntegerQ[m]


Int[u_^m_.*(a_.+b_.*Tanh[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Tanh[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*(a_.+b_.*Coth[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Coth[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*Tanh[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(c+d*x)^m*(a+b*Tanh[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*Coth[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(c+d*x)^m*(a+b*Coth[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]





(* ::Subsection::Closed:: *)
(*2.11 (e x)^m (a+b tanh(c+d x^n))^p*)


Int[(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Tanh[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && PositiveIntegerQ[1/n] && IntegerQ[p]


Int[(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Coth[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && PositiveIntegerQ[1/n] && IntegerQ[p]


Int[(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][(a+b*Tanh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][(a+b*Coth[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Tanh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Tanh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+b_.*Coth[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Coth[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+b_.*Tanh[u_])^p_.,x_Symbol] :=
  Int[(a+b*Tanh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*Coth[u_])^p_.,x_Symbol] :=
  Int[(a+b*Coth[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Tanh[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Coth[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]] && IntegerQ[p]


Int[x_^m_.*Tanh[c_.+d_.*x_^n_]^2,x_Symbol] :=
  -x^(m-n+1)*Tanh[c+d*x^n]/(d*n) + Int[x^m,x] + (m-n+1)/(d*n)*Int[x^(m-n)*Tanh[c+d*x^n],x] /;
FreeQ[{c,d,m,n},x]


Int[x_^m_.*Coth[c_.+d_.*x_^n_]^2,x_Symbol] :=
  -x^(m-n+1)*Coth[c+d*x^n]/(d*n) + Int[x^m,x] + (m-n+1)/(d*n)*Int[x^(m-n)*Coth[c+d*x^n],x] /;
FreeQ[{c,d,m,n},x]


Int[x_^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*Tanh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[x_^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*Coth[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Tanh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Coth[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Tanh[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Tanh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(e_*x_)^m_.*(a_.+b_.*Coth[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Coth[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_.*Tanh[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
  -x^(m-n+1)*Sech[a+b*x^n]^p/(b*n*p) +
  (m-n+1)/(b*n*p)*Int[x^(m-n)*Sech[a+b*x^n]^p,x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1


Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_.*Coth[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
  -x^(m-n+1)*Csch[a+b*x^n]^p/(b*n*p) +
  (m-n+1)/(b*n*p)*Int[x^(m-n)*Csch[a+b*x^n]^p,x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1





(* ::Subsection::Closed:: *)
(*2.12 (d+e x)^m tanh(a+b x+c x^2)^n*)
(**)


Int[Tanh[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][Tanh[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,n},x]


Int[Coth[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][Coth[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,n},x]


Int[(d_.+e_.*x_)*Tanh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Log[Cosh[a+b*x+c*x^2]]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Tanh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)*Coth[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Log[Sinh[a+b*x+c*x^2]]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Coth[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x]


(* Int[x_^m_*Tanh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  x^(m-1)*Log[Cosh[a+b*x+c*x^2]]/(2*c) -
  b/(2*c)*Int[x^(m-1)*Tanh[a+b*x+c*x^2],x] -
  (m-1)/(2*c)*Int[x^(m-2)*Log[Cosh[a+b*x+c*x^2]],x] /;
FreeQ[{a,b,c},x] && RationalQ[m] && m>1 *)


(* Int[x_^m_*Coth[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  x^(m-1)*Log[Sinh[a+b*x+c*x^2]]/(2*c) -
  b/(2*c)*Int[x^(m-1)*Coth[a+b*x+c*x^2],x] -
  (m-1)/(2*c)*Int[x^(m-2)*Log[Sinh[a+b*x+c*x^2]],x] /;
FreeQ[{a,b,c},x] && RationalQ[m] && m>1 *)


Int[(d_.+e_.*x_)^m_.*Tanh[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*Tanh[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(d_.+e_.*x_)^m_.*Coth[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*Coth[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]





(* ::Subsection::Closed:: *)
(*3.10 (c+d x)^m (a+b sech)^n*)


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_],x_Symbol] :=
  2*(c+d*x)^m*ArcTan[E^(a+b*x)]/b - 
  I*d*m/b*Int[(c+d*x)^(m-1)*Log[1-I*E^(a+b*x)],x] + 
  I*d*m/b*Int[(c+d*x)^(m-1)*Log[1+I*E^(a+b*x)],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_],x_Symbol] :=
  -2*(c+d*x)^m*ArcTanh[E^(a+b*x)]/b - 
  d*m/b*Int[(c+d*x)^(m-1)*Log[1-E^(a+b*x)],x] + 
  d*m/b*Int[(c+d*x)^(m-1)*Log[1+E^(a+b*x)],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^2,x_Symbol] :=
  (c+d*x)^m*Tanh[a+b*x]/b - 
  d*m/b*Int[(c+d*x)^(m-1)*Tanh[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^2,x_Symbol] :=
  -(c+d*x)^m*Coth[a+b*x]/b + 
  d*m/b*Int[(c+d*x)^(m-1)*Coth[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)*Tanh[a+b*x]*Sech[a+b*x]^(n-2)/(b*(n-1)) +
  d*Sech[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  (n-2)/(n-1)*Int[(c+d*x)*Sech[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1 && n!=2


Int[(c_.+d_.*x_)*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)*Coth[a+b*x]*Csch[a+b*x]^(n-2)/(b*(n-1)) -
  d*Csch[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) -
  (n-2)/(n-1)*Int[(c+d*x)*Csch[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1 && n!=2


Int[(c_.+d_.*x_)^m_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^m*Tanh[a+b*x]*Sech[a+b*x]^(n-2)/(b*(n-1)) +
  d*m*(c+d*x)^(m-1)*Sech[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  (n-2)/(n-1)*Int[(c+d*x)^m*Sech[a+b*x]^(n-2),x] -
  d^2*m*(m-1)/(b^2*(n-1)*(n-2))*Int[(c+d*x)^(m-2)*Sech[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && n!=2 && m>1


Int[(c_.+d_.*x_)^m_*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)^m*Coth[a+b*x]*Csch[a+b*x]^(n-2)/(b*(n-1)) -
  d*m*(c+d*x)^(m-1)*Csch[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) -
  (n-2)/(n-1)*Int[(c+d*x)^m*Csch[a+b*x]^(n-2),x] +
  d^2*m*(m-1)/(b^2*(n-1)*(n-2))*Int[(c+d*x)^(m-2)*Csch[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && n!=2 && m>1


Int[(c_.+d_.*x_)*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
  -d*Sech[a+b*x]^n/(b^2*n^2) -
  (c+d*x)*Sinh[a+b*x]*Sech[a+b*x]^(n+1)/(b*n) +
  (n+1)/n*Int[(c+d*x)*Sech[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1


Int[(c_.+d_.*x_)*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
  -d*Csch[a+b*x]^n/(b^2*n^2) -
  (c+d*x)*Cosh[a+b*x]*Csch[a+b*x]^(n+1)/(b*n) -
  (n+1)/n*Int[(c+d*x)*Csch[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1


Int[(c_.+d_.*x_)^m_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
  -d*m*(c+d*x)^(m-1)*Sech[a+b*x]^n/(b^2*n^2) -
  (c+d*x)^m*Sinh[a+b*x]*Sech[a+b*x]^(n+1)/(b*n) +
  (n+1)/n*Int[(c+d*x)^m*Sech[a+b*x]^(n+2),x] +
  d^2*m*(m-1)/(b^2*n^2)*Int[(c+d*x)^(m-2)*Sech[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n<-1 && m>1


Int[(c_.+d_.*x_)^m_*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
  -d*m*(c+d*x)^(m-1)*Csch[a+b*x]^n/(b^2*n^2) -
  (c+d*x)^m*Cosh[a+b*x]*Csch[a+b*x]^(n+1)/(b*n) -
  (n+1)/n*Int[(c+d*x)^m*Csch[a+b*x]^(n+2),x] +
  d^2*m*(m-1)/(b^2*n^2)*Int[(c+d*x)^(m-2)*Csch[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n<-1 && m>1


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
  Cosh[a+b*x]^n*Sech[a+b*x]^n*Int[(c+d*x)^m/Cosh[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
  Sinh[a+b*x]^n*Csch[a+b*x]^n*Int[(c+d*x)^m/Sinh[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Sech[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*Sech[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[m,n]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Csch[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*Csch[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[m,n]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Sech[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,Cosh[e+f*x]^(-n)/(b+a*Cosh[e+f*x])^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NegativeIntegerQ[n] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*Csch[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,Sinh[e+f*x]^(-n)/(b+a*Sinh[e+f*x])^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NegativeIntegerQ[n] && PositiveIntegerQ[m]


Int[u_^m_.*Sech[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Sech[ExpandToSum[v,x]]^n,x] /;
FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*Csch[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Csch[ExpandToSum[v,x]]^n,x] /;
FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.,x_Symbol] :=
  Defer[Int][(c+d*x)^m*Sech[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.,x_Symbol] :=
  Defer[Int][(c+d*x)^m*Csch[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]





(* ::Subsection::Closed:: *)
(*3.11 (e x)^m (a+b sech(c+d x^n))^p*)
(**)


Int[(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Sech[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && PositiveIntegerQ[1/n] && IntegerQ[p]


Int[(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Csch[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && PositiveIntegerQ[1/n] && IntegerQ[p]


Int[(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][(a+b*Sech[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][(a+b*Csch[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Sech[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Sech[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+b_.*Csch[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Csch[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+b_.*Sech[u_])^p_.,x_Symbol] :=
  Int[(a+b*Sech[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*Csch[u_])^p_.,x_Symbol] :=
  Int[(a+b*Csch[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Sech[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Csch[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*Sech[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[x_^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*Csch[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sech[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Csch[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Sech[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Sech[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(e_*x_)^m_.*(a_.+b_.*Csch[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Csch[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Sech[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Sech[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]


Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Csch[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Csch[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]





(* ::Subsection::Closed:: *)
(*4.5 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p*)


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Cosh[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*Sinh[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Sinh[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]*Cosh[a_.+b_.*x_]^n_.,x_Symbol] :=
  (c+d*x)^m*Cosh[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Cosh[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Cosh[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Sinh[a+b*x]^n*Cosh[a+b*x]^p,x],x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[(c+d*x)^m*Sinh[a+b*x]^n*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sinh[a+b*x]^(n-2)*Tanh[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Cosh[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[(c+d*x)^m*Cosh[a+b*x]^n*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Cosh[a+b*x]^(n-2)*Coth[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
  -(c+d*x)^m*Sech[a+b*x]^n/(b*n) + 
  d*m/(b*n)*Int[(c+d*x)^(m-1)*Sech[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && p===1 && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
  -(c+d*x)^m*Csch[a+b*x]^n/(b*n) + 
  d*m/(b*n)*Int[(c+d*x)^(m-1)*Csch[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && p===1 && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^2*Tanh[a_.+b_.*x_]^n_.,x_Symbol] :=
  (c+d*x)^m*Tanh[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Tanh[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^2*Coth[a_.+b_.*x_]^n_.,x_Symbol] :=
  -(c+d*x)^m*Coth[a+b*x]^(n+1)/(b*(n+1)) + 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Coth[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]*Tanh[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[(c+d*x)^m*Sech[a+b*x]*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sech[a+b*x]^3*Tanh[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[(c+d*x)^m*Sech[a+b*x]^n*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sech[a+b*x]^(n+2)*Tanh[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]*Coth[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[(c+d*x)^m*Csch[a+b*x]*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csch[a+b*x]^3*Coth[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[(c+d*x)^m*Csch[a+b*x]^n*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csch[a+b*x]^(n+2)*Coth[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
  With[{u=IntHide[Sech[a+b*x]^n*Tanh[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d,n,p},x] && PositiveIntegerQ[m] && (EvenQ[n] || OddQ[p])


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
  With[{u=IntHide[Csch[a+b*x]^n*Coth[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d,n,p},x] && PositiveIntegerQ[m] && (EvenQ[n] || OddQ[p])


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Sech[a_.+b_.*x_]^n_., x_Symbol] :=
  2^n*Int[(c+d*x)^m*Csch[2*a+2*b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && IntegerQ[n]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Sech[a_.+b_.*x_]^p_., x_Symbol] :=
  With[{u=IntHide[Csch[a+b*x]^n*Sech[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && RationalQ[m] && m>0 && n!=p


Int[u_^m_.*F_[v_]^n_.*G_[w_]^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F[ExpandToSum[v,x]]^n*G[ExpandToSum[v,x]]^p,x] /;
FreeQ[{m,n,p},x] && HyperbolicQ[F] && HyperbolicQ[G] && ZeroQ[v-w] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]*(a_+b_.*Sinh[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Sinh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Sinh[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]*(a_+b_.*Cosh[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Cosh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Cosh[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^2*(a_+b_.*Tanh[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Tanh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Tanh[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^2*(a_+b_.*Coth[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Coth[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Coth[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]*Tanh[c_.+d_.*x_]*(a_+b_.*Sech[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Sech[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Sech[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]*Coth[c_.+d_.*x_]*(a_+b_.*Csch[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Csch[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Csch[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]^p_.*Sinh[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Sinh[a+b*x]^p*Sinh[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[p,q] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Cosh[a+b*x]^p*Cosh[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[p,q] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Sinh[a+b*x]^p*Cosh[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[p,q]


Int[(e_.+f_.*x_)^m_.*F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigExpand[(e+f*x)^m*G[c+d*x]^q,F,c+d*x,p,b/d,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && MemberQ[{Sinh,Cosh},F] && MemberQ[{Sech,Csch},G] && 
  PositiveIntegerQ[p,q] && ZeroQ[b*c-a*d] && PositiveIntegerQ[b/d-1]





(* ::Subsection::Closed:: *)
(*4.6 F^(c (a+b x)) hyper(d+e x)^n*)


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_],x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) + 
  e*F^(c*(a+b*x))*Cosh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2-b^2*c^2*Log[F]^2]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_],x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) + 
  e*F^(c*(a+b*x))*Sinh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2-b^2*c^2*Log[F]^2]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2) + 
  e*n*F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n-1)/(e^2*n^2-b^2*c^2*Log[F]^2) - 
  n*(n-1)*e^2/(e^2*n^2-b^2*c^2*Log[F]^2)*Int[F^(c*(a+b*x))*Sinh[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*n^2-b^2*c^2*Log[F]^2] && RationalQ[n] && n>1


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2) + 
  e*n*F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n-1)/(e^2*n^2-b^2*c^2*Log[F]^2) + 
  n*(n-1)*e^2/(e^2*n^2-b^2*c^2*Log[F]^2)*Int[F^(c*(a+b*x))*Cosh[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*n^2-b^2*c^2*Log[F]^2] && RationalQ[n] && n>1


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) + 
  F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n+1)/(e*(n+1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && ZeroQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) - 
  F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n+1)/(e*(n+1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && ZeroQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) + 
  F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n+1)/(e*(n+1)) - 
  (e^2*(n+2)^2-b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2))*Int[F^(c*(a+b*x))*Sinh[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1 && n!=-2


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) - 
  F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n+1)/(e*(n+1)) + 
  (e^2*(n+2)^2-b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2))*Int[F^(c*(a+b*x))*Cosh[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1 && n!=-2


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
  E^(n*(d+e*x))*Sinh[d+e*x]^n/(-1+E^(2*(d+e*x)))^n*Int[F^(c*(a+b*x))*(-1+E^(2*(d+e*x)))^n/E^(n*(d+e*x)),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
  E^(n*(d+e*x))*Cosh[d+e*x]^n/(1+E^(2*(d+e*x)))^n*Int[F^(c*(a+b*x))*(1+E^(2*(d+e*x)))^n/E^(n*(d+e*x)),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Tanh[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandIntegrand[F^(c*(a+b*x))*(-1+E^(2*(d+e*x)))^n/(1+E^(2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Coth[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandIntegrand[F^(c*(a+b*x))*(1+E^(2*(d+e*x)))^n/(-1+E^(2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*(Sech[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2)) - 
  e*n*F^(c*(a+b*x))*Sech[d+e*x]^(n+1)*(Sinh[d+e*x]/(e^2*n^2-b^2*c^2*Log[F]^2)) + 
  e^2*n*((n+1)/(e^2*n^2-b^2*c^2*Log[F]^2))*Int[F^(c*(a+b*x))*Sech[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*n^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*(Csch[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2)) - 
  e*n*F^(c*(a+b*x))*Csch[d+e*x]^(n+1)*(Cosh[d+e*x]/(e^2*n^2-b^2*c^2*Log[F]^2)) - 
  e^2*n*((n+1)/(e^2*n^2-b^2*c^2*Log[F]^2))*Int[F^(c*(a+b*x))*Csch[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*n^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Sech[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Sech[d+e*x]^(n-1)*Sinh[d+e*x]/(e*(n-1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && ZeroQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2] && NonzeroQ[n-1] && NonzeroQ[n-2]


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Csch[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) - 
  F^(c*(a+b*x))*Csch[d+e*x]^(n-1)*Cosh[d+e*x]/(e*(n-1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && ZeroQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2] && NonzeroQ[n-1] && NonzeroQ[n-2]


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Sech[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Sech[d+e*x]^(n-1)*Sinh[d+e*x]/(e*(n-1)) +
  (e^2*(n-2)^2-b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2))*Int[F^(c*(a+b*x))*Sech[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2] && RationalQ[n] && n>1 && n!=2


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Csch[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) - 
  F^(c*(a+b*x))*Csch[d+e*x]^(n-1)*Cosh[d+e*x]/(e*(n-1)) -
  (e^2*(n-2)^2-b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2))*Int[F^(c*(a+b*x))*Csch[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2] && RationalQ[n] && n>1 && n!=2


(* Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(n*(d+e*x))/(1+E^(2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n] *)


(* Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-n*(d+e*x))/(1-E^(-2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n] *)


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*E^(n*(d+e*x))*F^(c*(a+b*x))/(e*n+b*c*Log[F])*Hypergeometric2F1[n,n/2+b*c*Log[F]/(2*e),1+n/2+b*c*Log[F]/(2*e),-E^(2*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_.,x_Symbol] :=
  (-2)^n*E^(n*(d+e*x))*F^(c*(a+b*x))/(e*n+b*c*Log[F])*Hypergeometric2F1[n,n/2+b*c*Log[F]/(2*e),1+n/2+b*c*Log[F]/(2*e),E^(2*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_.,x_Symbol] :=
  (1+E^(2*(d+e*x)))^n*Sech[d+e*x]^n/E^(n*(d+e*x))*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(n*(d+e*x))/(1+E^(2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_.,x_Symbol] :=
  (1-E^(-2*(d+e*x)))^n*Csch[d+e*x]^n/E^(-n*(d+e*x))*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-n*(d+e*x))/(1-E^(-2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Sinh[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*f^n*Int[F^(c*(a+b*x))*Cosh[d/2+e*x/2-f*Pi/(4*g)]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f^2+g^2] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*g^n*Int[F^(c*(a+b*x))*Cosh[d/2+e*x/2]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f-g] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*g^n*Int[F^(c*(a+b*x))*Sinh[d/2+e*x/2]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f+g] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^m_.*(f_+g_.*Sinh[d_.+e_.*x_])^n_.,x_Symbol] :=
  g^n*Int[F^(c*(a+b*x))*Tanh[d/2+e*x/2-f*Pi/(4*g)]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f^2+g^2] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
  g^n*Int[F^(c*(a+b*x))*Tanh[d/2+e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f-g] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
  g^n*Int[F^(c*(a+b*x))*Coth[d/2+e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f+g] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Cosh[d_.+e_.*x_])/(f_+g_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
  2*i*Int[F^(c*(a+b*x))*(Cosh[d+e*x]/(f+g*Sinh[d+e*x])),x] + 
  Int[F^(c*(a+b*x))*((h-i*Cosh[d+e*x])/(f+g*Sinh[d+e*x])),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && ZeroQ[f^2+g^2] && ZeroQ[h^2-i^2] && ZeroQ[g*h-f*i]


Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Sinh[d_.+e_.*x_])/(f_+g_.*Cosh[d_.+e_.*x_]),x_Symbol] :=
  2*i*Int[F^(c*(a+b*x))*(Sinh[d+e*x]/(f+g*Cosh[d+e*x])),x] + 
  Int[F^(c*(a+b*x))*((h-i*Sinh[d+e*x])/(f+g*Cosh[d+e*x])),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && ZeroQ[f^2-g^2] && ZeroQ[h^2+i^2] && ZeroQ[g*h+f*i]


Int[F_^(c_.*u_)*G_[v_]^n_.,x_Symbol] :=
  Int[F^(c*ExpandToSum[u,x])*G[ExpandToSum[v,x]]^n,x] /;
FreeQ[{F,c,n},x] && HyperbolicQ[G] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[x_^m_.*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_.,x_Symbol] :=
  With[{u=IntHide[F^(c*(a+b*x))*Sinh[d+e*x]^n,x]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]] /;
FreeQ[{F,a,b,c,d,e},x] && RationalQ[m] && m>0 && PositiveIntegerQ[n]


Int[x_^m_.*F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_.,x_Symbol] :=
  With[{u=IntHide[F^(c*(a+b*x))*Cosh[d+e*x]^n,x]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]] /;
FreeQ[{F,a,b,c,d,e},x] && RationalQ[m] && m>0 && PositiveIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*Cosh[f_.+g_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[F^(c*(a+b*x)),Sinh[d+e*x]^m*Cosh[f+g*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && PositiveIntegerQ[m,n]


Int[x_^p_.*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*Cosh[f_.+g_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^p*F^(c*(a+b*x)),Sinh[d+e*x]^m*Cosh[f+g*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && PositiveIntegerQ[m,n,p]


Int[F_^(c_.*(a_.+b_.*x_))*G_[d_.+e_.*x_]^m_.*H_[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^(c*(a+b*x)),G[d+e*x]^m*H[d+e*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && PositiveIntegerQ[m,n] && HyperbolicQ[G] && HyperbolicQ[H]


Int[F_^u_*Sinh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Sinh[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && PositiveIntegerQ[n]


Int[F_^u_*Cosh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Cosh[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && PositiveIntegerQ[n]


Int[F_^u_*Sinh[v_]^m_.*Cosh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Sinh[v]^m*Cosh[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && PositiveIntegerQ[m,n]





(* ::Subsection::Closed:: *)
(*4.7 x^m hyper(a+b log(c x^n))^p*)


Int[Sinh[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[((c*x^n)^b/2 - 1/(2*(c*x^n)^b))^p,x] /;
FreeQ[c,x] && RationalQ[b,n,p]


Int[Cosh[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[((c*x^n)^b/2 + 1/(2*(c*x^n)^b))^p,x] /;
FreeQ[c,x] && RationalQ[b,n,p]


Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*(p+2)*Sinh[a+b*Log[c*x^n]]^(p+2)/(p+1) + 
  x*Coth[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[b^2*n^2*(p+2)^2-1] && NonzeroQ[p+1]


Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(p+2)*Cosh[a+b*Log[c*x^n]]^(p+2)/(p+1) - 
  x*Tanh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[b^2*n^2*(p+2)^2-1] && NonzeroQ[p+1]


Int[Sqrt[Sinh[a_.+b_.*Log[c_.*x_^n_.]]],x_Symbol] :=
  x*Sqrt[Sinh[a+b*Log[c*x^n]]]/Sqrt[-1+E^(2*a)*(c*x^n)^(4/n)]*
    Int[Sqrt[-1+E^(2*a)*(c*x^n)^(4/n)]/x,x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[b*n-2]


Int[Sqrt[Cosh[a_.+b_.*Log[c_.*x_^n_.]]],x_Symbol] :=
  x*Sqrt[Cosh[a+b*Log[c*x^n]]]/Sqrt[1+E^(2*a)*(c*x^n)^(4/n)]*
    Int[Sqrt[1+E^(2*a)*(c*x^n)^(4/n)]/x,x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[b*n-2]


Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(-E^(-a*b*n*p)/(2*b*n*p)*(c*x^n)^(-1/(n*p)) + E^(a*b*n*p)/(2*b*n*p)*(c*x^n)^(1/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[p] && ZeroQ[b^2*n^2*p^2-1]


Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(E^(-a*b*n*p)/2*(c*x^n)^(-1/(n*p)) + E^(a*b*n*p)/2*(c*x^n)^(1/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[p] && ZeroQ[b^2*n^2*p^2-1]


Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  -x*Sinh[a+b*Log[c*x^n]]/(b^2*n^2-1) +
  b*n*x*Cosh[a+b*Log[c*x^n]]/(b^2*n^2-1) /;
FreeQ[{a,b,c,n},x] && NonzeroQ[b^2*n^2-1]


Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  -x*Cosh[a+b*Log[c*x^n]]/(b^2*n^2-1) +
  b*n*x*Sinh[a+b*Log[c*x^n]]/(b^2*n^2-1) /;
FreeQ[{a,b,c,n},x] && NonzeroQ[b^2*n^2-1]


Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*Sinh[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-1) + 
  b*n*p*x*Cosh[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2-1) - 
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2-1)*Int[Sinh[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && NonzeroQ[b^2*n^2*p^2-1]


Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*Cosh[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-1) + 
  b*n*p*x*Sinh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2-1) + 
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2-1)*Int[Cosh[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && NonzeroQ[b^2*n^2*p^2-1]


Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Coth[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  x*Sinh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) -
  (b^2*n^2*(p+2)^2-1)/(b^2*n^2*(p+1)*(p+2))*Int[Sinh[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[b^2*n^2*(p+2)^2-1]


Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*Tanh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) +
  x*Cosh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2-1)/(b^2*n^2*(p+1)*(p+2))*Int[Cosh[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[b^2*n^2*(p+2)^2-1]


Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(-E^(-a)*(c*x^n)^(-b)+E^a*(c*x^n)^b)^p/((b*n*p+1)*(2-2*E^(-2*a)*(c*x^n)^(-2*b))^p)*
    Hypergeometric2F1[-p,-(1+b*n*p)/(2*b*n),1-(1+b*n*p)/(2*b*n),E^(-2*a)*(c*x^n)^(-2*b)] /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[b^2*n^2*p^2-1]


Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(E^(-a)*(c*x^n)^(-b)+E^a*(c*x^n)^b)^p/((b*n*p+1)*(2+2*E^(-2*a)*(c*x^n)^(-2*b))^p)*
    Hypergeometric2F1[-p,-(1+b*n*p)/(2*b*n),1-(1+b*n*p)/(2*b*n),-E^(-2*a)*(c*x^n)^(-2*b)] /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[b^2*n^2*p^2-1]


Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -(p+2)*x^(m+1)*Sinh[a+b*Log[c*x^n]]^(p+2)/((m+1)*(p+1)) + 
  x^(m+1)*Coth[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[b^2*n^2*(p+2)^2-(m+1)^2] && NonzeroQ[p+1] && NonzeroQ[m+1]


Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p+2)*x^(m+1)*Cosh[a+b*Log[c*x^n]]^(p+2)/((m+1)*(p+1)) - 
  x^(m+1)*Tanh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[b^2*n^2*(p+2)^2-(m+1)^2] && NonzeroQ[p+1] && NonzeroQ[m+1]


Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  1/2^p*Int[ExpandIntegrand[x^m*(-(m+1)/(b*n*p)*E^(-a*b*n*p/(m+1))*(c*x^n)^(-(m+1)/(n*p)) + 
    (m+1)/(b*n*p)*E^((a*b*n*p)/(m+1))*(c*x^n)^((m+1)/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p] && ZeroQ[b^2*n^2*p^2-(m+1)^2]


Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  1/2^p*Int[ExpandIntegrand[x^m*(E^((a*b*n*p)/(m+1))*(c*x^n)^((m+1)/(n*p)) + 
    E^(-a*b*n*p/(m+1))*(c*x^n)^(-(m+1)/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p] && ZeroQ[b^2*n^2*p^2-(m+1)^2]


Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  -(m+1)*x^(m+1)*Sinh[a+b*Log[c*x^n]]/(b^2*n^2-(m+1)^2) + 
  b*n*x^(m+1)*Cosh[a+b*Log[c*x^n]]/(b^2*n^2-(m+1)^2) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2*n^2-(m+1)^2] && NonzeroQ[m+1]


Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  -(m+1)*x^(m+1)*Cosh[a+b*Log[c*x^n]]/(b^2*n^2-(m+1)^2) + 
  b*n*x^(m+1)*Sinh[a+b*Log[c*x^n]]/(b^2*n^2-(m+1)^2) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2*n^2-(m+1)^2] && NonzeroQ[m+1]


Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -(m+1)*x^(m+1)*Sinh[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-(m+1)^2) + 
  b*n*p*x^(m+1)*Cosh[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2-(m+1)^2) - 
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2-(m+1)^2)*Int[x^m*Sinh[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2*n^2*p^2-(m+1)^2] && RationalQ[p] && p>1 && NonzeroQ[m+1]


Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -(m+1)*x^(m+1)*Cosh[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-(m+1)^2) + 
  b*n*p*x^(m+1)*Cosh[a+b*Log[c*x^n]]^(p-1)*Sinh[a+b*Log[c*x^n]]/(b^2*n^2*p^2-(m+1)^2) + 
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2-(m+1)^2)*Int[x^m*Cosh[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2*n^2*p^2-(m+1)^2] && RationalQ[p] && p>1 && NonzeroQ[m+1]


Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*Coth[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) - 
  (m+1)*x^(m+1)*Sinh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) - 
  (b^2*n^2*(p+2)^2-(m+1)^2)/(b^2*n^2*(p+1)*(p+2))*Int[x^m*Sinh[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2*n^2*(p+2)^2-(m+1)^2] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[m+1]


Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x^(m+1)*Tanh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) + 
  (m+1)*x^(m+1)*Cosh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) + 
  (b^2*n^2*(p+2)^2-(m+1)^2)/(b^2*n^2*(p+1)*(p+2))*Int[x^m*Cosh[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2*n^2*(p+2)^2-(m+1)^2] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[m+1]


Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*(-E^(-a)*(c*x^n)^(-b)+E^a*(c*x^n)^b)^p/((m+b*n*p+1)*(2-2*E^(-2*a)*(c*x^n)^(-2*b))^p)*
    Hypergeometric2F1[-p,-(m+b*n*p+1)/(2*b*n),1-(m+b*n*p+1)/(2*b*n),E^(-2*a)*(c*x^n)^(-2*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[b^2*n^2*p^2-(m+1)^2]


Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*(E^(-a)*(c*x^n)^(-b)+E^a*(c*x^n)^b)^p/((m+b*n*p+1)*(2+2*E^(-2*a)*(c*x^n)^(-2*b))^p)*
    Hypergeometric2F1[-p,-(m+b*n*p+1)/(2*b*n),1-(m+b*n*p+1)/(2*b*n),-E^(-2*a)*(c*x^n)^(-2*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[b^2*n^2*p^2-(m+1)^2]


Int[Sech[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  2^p*Int[((c*x^n)^b/(1+(c*x^n)^(2*b)))^p,x] /;
FreeQ[c,x] && RationalQ[b,n,p]


Int[Csch[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  2^p*Int[((c*x^n)^b/(-1+(c*x^n)^(2*b)))^p,x] /;
FreeQ[c,x] && RationalQ[b,n,p]


Int[Sech[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*E^(-a*b*n)*Int[(c*x^n)^(1/n)/(E^(-2*a*b*n)+(c*x^n)^(2/n)),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[b^2*n^2-1]


Int[Csch[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  -2*b*n*E^(-a*b*n)*Int[(c*x^n)^(1/n)/(E^(-2*a*b*n)-(c*x^n)^(2/n)),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[b^2*n^2-1]


Int[Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x*Sech[a+b*Log[c*x^n]]^(p-2)/(p-1) + 
  x*Tanh[a+b*Log[c*x^n]]*Sech[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[b^2*n^2*(p-2)^2-1] && NonzeroQ[p-1]


Int[Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -(p-2)*x*Csch[a+b*Log[c*x^n]]^(p-2)/(p-1) - 
  x*Coth[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[b^2*n^2*(p-2)^2-1] && NonzeroQ[p-1]


Int[Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Tanh[a+b*Log[c*x^n]]*Sech[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) +
  x*Sech[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2-1)/(b^2*n^2*(p-1)*(p-2))*Int[Sech[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2-1]


Int[Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*Coth[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Csch[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) -
  (b^2*n^2*(p-2)^2-1)/(b^2*n^2*(p-1)*(p-2))*Int[Csch[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2-1]


Int[Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -b*n*p*x*Sech[a+b*Log[c*x^n]]^(p+1)*Sinh[a+b*Log[c*x^n]]/(b^2*n^2*p^2-1) -
  x*Sech[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-1) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2-1)*Int[Sech[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2-1]


Int[Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -b*n*p*x*Cosh[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2-1) - 
  x*Csch[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-1) -
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2-1)*Int[Csch[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2-1]


Int[Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  2^p*x*(E^(2*a)*(c*x^n)^(2*b)+1)^p/(b*n*p+1)*(E^a*(c*x^n)^b/(E^(2*a)*(c*x^n)^(2*b)+1))^p*
    Hypergeometric2F1[p,(b*n*p+1)/(2*b*n),1+(b*n*p+1)/(2*b*n),-E^(2*a)*(c*x^n)^(2*b)] /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[b^2*n^2*p^2-1]


Int[Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x*(2-2*E^(2*a)*(c*x^n)^(2*b))^p/(b*n*p+1)*(E^a*(c*x^n)^b/(E^(2*a)*(c*x^n)^(2*b)-1))^p*
    Hypergeometric2F1[p,(b*n*p+1)/(2*b*n),1+(b*n*p+1)/(2*b*n),E^(2*a)*(c*x^n)^(2*b)] /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[b^2*n^2*p^2-1]


Int[x_^m_.*Sech[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  2^p*Int[x^m*((c*x^n)^b/(1+(c*x^n)^(2*b)))^p,x] /;
FreeQ[c,x] && RationalQ[b,m,n,p]


Int[x_^m_.*Csch[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  2^p*Int[x^m*((c*x^n)^b/(-1+(c*x^n)^(2*b)))^p,x] /;
FreeQ[c,x] && RationalQ[b,m,n,p]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*E^(-a*b*n/(m+1))*Int[x^m*(c*x^n)^((m+1)/n)/(E^(-2*a*b*n/(m+1))+(c*x^n)^(2*(m+1)/n)),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[b^2*n^2-(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  -2*b*n/(m+1)*E^(-a*b*n/(m+1))*Int[x^m*(c*x^n)^((m+1)/n)/(E^(-2*a*b*n/(m+1))-(c*x^n)^(2*(m+1)/n)),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[b^2*n^2-(m+1)^2]


Int[x_^m_.*Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x^(m+1)*Sech[a+b*Log[c*x^n]]^(p-2)/((m+1)*(p-1)) + 
  x^(m+1)*Tanh[a+b*Log[c*x^n]]*Sech[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[b^2*n^2*(p-2)^2+(m+1)^2] && NonzeroQ[m+1] && NonzeroQ[p-1]


Int[x_^m_.*Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -(p-2)*x^(m+1)*Csch[a+b*Log[c*x^n]]^(p-2)/((m+1)*(p-1)) - 
  x^(m+1)*Coth[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[b^2*n^2*(p-2)^2+(m+1)^2] && NonzeroQ[m+1] && NonzeroQ[p-1]


Int[x_^m_.*Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*Tanh[a+b*Log[c*x^n]]*Sech[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) +
  (m+1)*x^(m+1)*Sech[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2-(m+1)^2)/(b^2*n^2*(p-1)*(p-2))*Int[x^m*Sech[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2-(m+1)^2]


Int[x_^m_.*Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x^(m+1)*Coth[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  (m+1)*x^(m+1)*Csch[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) -
  (b^2*n^2*(p-2)^2-(m+1)^2)/(b^2*n^2*(p-1)*(p-2))*Int[x^m*Csch[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2-(m+1)^2]


Int[x_^m_.*Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -(m+1)*x^(m+1)*Sech[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-(m+1)^2) -
  b*n*p*x^(m+1)*Sech[a+b*Log[c*x^n]]^(p+1)*Sinh[a+b*Log[c*x^n]]/(b^2*n^2*p^2-(m+1)^2) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2-(m+1)^2)*Int[x^m*Sech[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2-(m+1)^2]


Int[x_^m_.*Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -(m+1)*x^(m+1)*Csch[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-(m+1)^2) -
  b*n*p*x^(m+1)*Cosh[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2-(m+1)^2) -
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2-(m+1)^2)*Int[x^m*Csch[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2-(m+1)^2]


Int[x_^m_.*Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  2^p*x^(m+1)*(E^(2*a)*(c*x^n)^(2*b)+1)^p/(m+b*n*p+1)*(E^a*(c*x^n)^b/(E^(2*a)*(c*x^n)^(2*b)+1))^p*
    Hypergeometric2F1[p,(m+b*n*p+1)/(2*b*n),1+(m+b*n*p+1)/(2*b*n),-E^(2*a)*(c*x^n)^(2*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[b^2*n^2*p^2-(m+1)^2]


Int[x_^m_.*Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  2^p*x^(m+1)*(-E^(2*a)*(c*x^n)^(2*b)+1)^p/(m+b*n*p+1)*(E^a*(c*x^n)^b/(E^(2*a)*(c*x^n)^(2*b)-1))^p*
    Hypergeometric2F1[p,(m+b*n*p+1)/(2*b*n),1+(m+b*n*p+1)/(2*b*n),E^(2*a)*(c*x^n)^(2*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[b^2*n^2*p^2-(m+1)^2]


Int[Sinh[a_.*x_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Cosh[a*x*Log[b*x]^p]/a - 
  p*Int[Sinh[a*x*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b},x] && RationalQ[p] && p>0


Int[Cosh[a_.*x_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sinh[a*x*Log[b*x]^p]/a - 
  p*Int[Cosh[a*x*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b},x] && RationalQ[p] && p>0


Int[Sinh[a_.*x_^n_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Cosh[a*x^n*Log[b*x]^p]/(a*n*x^(n-1)) - 
  p/n*Int[Sinh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] + 
  (n-1)/(a*n)*Int[Cosh[a*x^n*Log[b*x]^p]/x^n,x] /;
FreeQ[{a,b},x] && RationalQ[n,p] && p>0


Int[Cosh[a_.*x_^n_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sinh[a*x^n*Log[b*x]^p]/(a*n*x^(n-1)) - 
  p/n*Int[Cosh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] + 
  (n-1)/(a*n)*Int[Sinh[a*x^n*Log[b*x]^p]/x^n,x] /;
FreeQ[{a,b},x] && RationalQ[n,p] && p>0


Int[x_^m_.*Sinh[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -Cosh[a*x^n*Log[b*x]^p]/(a*n) - 
  p/n*Int[x^(n-1)*Sinh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-n+1] && RationalQ[p] && p>0


Int[x_^m_.*Cosh[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sinh[a*x^n*Log[b*x]^p]/(a*n) - 
  p/n*Int[x^(n-1)*Cosh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-n+1] && RationalQ[p] && p>0


Int[x_^m_*Sinh[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  x^(m-n+1)*Cosh[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Sinh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] -
  (m-n+1)/(a*n)*Int[x^(m-n)*Cosh[a*x^n*Log[b*x]^p],x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p>0 && NonzeroQ[m-n+1]


Int[x_^m_*Cosh[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  x^(m-n+1)*Sinh[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Cosh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] -
  (m-n+1)/(a*n)*Int[x^(m-n)*Sinh[a*x^n*Log[b*x]^p],x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p>0 && NonzeroQ[m-n+1]


(* ::Subsection::Closed:: *)
(*4.8 Active hyperbolic functions*)


Int[Sinh[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Sinh[a*x]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[n]


Int[Cosh[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Cosh[a*x]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[n]


Int[Sinh[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Sinh[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n] && NonzeroQ[b*c-a*d]


Int[Cosh[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Cosh[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n] && NonzeroQ[b*c-a*d]


Int[Sinh[u_]^n_.,x_Symbol] :=
  With[{lst=QuotientOfLinearsParts[u,x]},
  Int[Sinh[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
PositiveIntegerQ[n] && QuotientOfLinearsQ[u,x]


Int[Cosh[u_]^n_.,x_Symbol] :=
  With[{lst=QuotientOfLinearsParts[u,x]},
  Int[Cosh[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
PositiveIntegerQ[n] && QuotientOfLinearsQ[u,x]


Int[u_.*Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
  Int[u*Sinh[v]^(p+q),x] /;
ZeroQ[v-w]


Int[u_.*Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[u*Cosh[v]^(p+q),x] /;
ZeroQ[v-w]


Int[Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Sinh[v]^p*Sinh[w]^q,x],x] /;
PositiveIntegerQ[p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Cosh[v]^p*Cosh[w]^q,x],x] /;
PositiveIntegerQ[p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sinh[v]^p*Sinh[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Cosh[v]^p*Cosh[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[u_.*Sinh[v_]^p_.*Cosh[w_]^p_.,x_Symbol] :=
  1/2^p*Int[u*Sinh[2*v]^p,x] /;
ZeroQ[v-w] && IntegerQ[p]


Int[Sinh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Sinh[v]^p*Cosh[w]^q,x],x] /;
PositiveIntegerQ[p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Sinh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sinh[v]^p*Cosh[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[Sinh[v_]*Tanh[w_]^n_.,x_Symbol] :=
  Int[Cosh[v]*Tanh[w]^(n-1),x] - Cosh[v-w]*Int[Sech[w]*Tanh[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Cosh[v_]*Coth[w_]^n_.,x_Symbol] :=
  Int[Sinh[v]*Coth[w]^(n-1),x] + Cosh[v-w]*Int[Csch[w]*Coth[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Sinh[v_]*Coth[w_]^n_.,x_Symbol] :=
  Int[Cosh[v]*Coth[w]^(n-1),x] + Sinh[v-w]*Int[Csch[w]*Coth[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Cosh[v_]*Tanh[w_]^n_.,x_Symbol] :=
  Int[Sinh[v]*Tanh[w]^(n-1),x] - Sinh[v-w]*Int[Sech[w]*Tanh[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Sinh[v_]*Sech[w_]^n_.,x_Symbol] :=
  Cosh[v-w]*Int[Tanh[w]*Sech[w]^(n-1),x] + Sinh[v-w]*Int[Sech[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Cosh[v_]*Csch[w_]^n_.,x_Symbol] :=
  Cosh[v-w]*Int[Coth[w]*Csch[w]^(n-1),x] + Sinh[v-w]*Int[Csch[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Sinh[v_]*Csch[w_]^n_.,x_Symbol] :=
  Sinh[v-w]*Int[Coth[w]*Csch[w]^(n-1),x] + Cosh[v-w]*Int[Csch[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Cosh[v_]*Sech[w_]^n_.,x_Symbol] :=
  Sinh[v-w]*Int[Tanh[w]*Sech[w]^(n-1),x] + Cosh[v-w]*Int[Sech[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sinh[c_.+d_.*x_]*Cosh[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(e+f*x)^m*(a+b*Sinh[2*c+2*d*x]/2)^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a-b+b*Cosh[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b] && IntegersQ[m,n] && m>0 && n<0 && (n==-1 || m==1 && n==-2)


Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a+b+b*Cosh[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b] && IntegersQ[m,n] && m>0 && n<0 && (n==-1 || m==1 && n==-2)


Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d^(m+1)*Subst[Int[(d*e-c*f+f*x)^m*Sinh[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && RationalQ[p]


Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d^(m+1)*Subst[Int[(d*e-c*f+f*x)^m*Cosh[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && RationalQ[p]


Int[(f_.+g_.*x_)^m_./(a_.+b_.*Cosh[d_.+e_.*x_]^2+c_.*Sinh[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[m] && NonzeroQ[a+b] && NonzeroQ[a+c]


Int[(f_.+g_.*x_)^m_.*Sech[d_.+e_.*x_]^2/(b_+c_.*Tanh[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{b,c,d,e,f,g},x] && PositiveIntegerQ[m]


Int[(f_.+g_.*x_)^m_.*Sech[d_.+e_.*x_]^2/(b_.+a_.*Sech[d_.+e_.*x_]^2+c_.*Tanh[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[m] && NonzeroQ[a+b] && NonzeroQ[a+c]


Int[(f_.+g_.*x_)^m_.*Csch[d_.+e_.*x_]^2/(c_+b_.*Coth[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{b,c,d,e,f,g},x] && PositiveIntegerQ[m]


Int[(f_.+g_.*x_)^m_.*Csch[d_.+e_.*x_]^2/(c_.+b_.*Coth[d_.+e_.*x_]^2+a_.*Csch[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[m] && NonzeroQ[a+b] && NonzeroQ[a+c]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  -(e+f*x)^(m+1)/(b*f*(m+1)) + 
  Int[(e+f*x)^m*E^(c+d*x)/(a-Rt[a^2+b^2,2]+b*E^(c+d*x)),x] + 
  Int[(e+f*x)^m*E^(c+d*x)/(a+Rt[a^2+b^2,2]+b*E^(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] (* && PosQ[a^2+b^2] *)


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  -(e+f*x)^(m+1)/(b*f*(m+1)) + 
  Int[(e+f*x)^m*E^(c+d*x)/(a-Rt[a^2-b^2,2]+b*E^(c+d*x)),x] + 
  Int[(e+f*x)^m*E^(c+d*x)/(a+Rt[a^2-b^2,2]+b*E^(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] (* && PosQ[a^2+b^2] *)


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^n_/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2),x] + 
  1/b*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1 && ZeroQ[a^2+b^2]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^n_/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2),x] + 
  1/b*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1 && ZeroQ[a^2-b^2]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^n_/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  -a/b^2*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2),x] + 
  1/b*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)*Sinh[c+d*x],x] + 
  (a^2+b^2)/b^2*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1 && NonzeroQ[a^2+b^2]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^n_/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  -a/b^2*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2),x] + 
  1/b*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)*Cosh[c+d*x],x] + 
  (a^2-b^2)/b^2*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1 && NonzeroQ[a^2-b^2]


Int[(e_.+f_.*x_)*(A_+B_.*Sinh[c_.+d_.*x_])/(a_+b_.*Sinh[c_.+d_.*x_])^2,x_Symbol] :=
  B*(e+f*x)*Cosh[c+d*x]/(a*d*(a+b*Sinh[c+d*x])) - 
  B*f/(a*d)*Int[Cosh[c+d*x]/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && ZeroQ[a*A+b*B]


Int[(e_.+f_.*x_)*(A_+B_.*Cosh[c_.+d_.*x_])/(a_+b_.*Cosh[c_.+d_.*x_])^2,x_Symbol] :=
  B*(e+f*x)*Sinh[c+d*x]/(a*d*(a+b*Cosh[c+d*x])) -
  B*f/(a*d)*Int[Sinh[c+d*x]/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && ZeroQ[a*A-b*B]


Int[Sech[v_]^m_.*(a_+b_.*Tanh[v_])^n_.,x_Symbol] :=
  Int[(a*Cosh[v]+b*Sinh[v])^n,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m+n==0 && OddQ[m]


Int[Csch[v_]^m_.*(a_+b_.*Coth[v_])^n_.,x_Symbol] :=
  Int[(b*Cosh[v]+a*Sinh[v])^n,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m+n==0 && OddQ[m]


Int[u_.*Sinh[a_.+b_.*x_]^m_.*Sinh[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[u,Sinh[a+b*x]^m*Sinh[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m,n]


Int[u_.*Cosh[a_.+b_.*x_]^m_.*Cosh[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[u,Cosh[a+b*x]^m*Cosh[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m,n]


Int[Sech[a_.+b_.*x_]*Sech[c_+d_.*x_],x_Symbol] :=
  -Csch[(b*c-a*d)/d]*Int[Tanh[a+b*x],x] + Csch[(b*c-a*d)/b]*Int[Tanh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b^2-d^2] && NonzeroQ[b*c-a*d]


Int[Csch[a_.+b_.*x_]*Csch[c_+d_.*x_],x_Symbol] :=
  Csch[(b*c-a*d)/b]*Int[Coth[a+b*x],x] - Csch[(b*c-a*d)/d]*Int[Coth[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b^2-d^2] && NonzeroQ[b*c-a*d]


Int[Tanh[a_.+b_.*x_]*Tanh[c_+d_.*x_],x_Symbol] :=
  b*x/d - b/d*Cosh[(b*c-a*d)/d]*Int[Sech[a+b*x]*Sech[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b^2-d^2] && NonzeroQ[b*c-a*d]


Int[Coth[a_.+b_.*x_]*Coth[c_+d_.*x_],x_Symbol] :=
  b*x/d + Cosh[(b*c-a*d)/d]*Int[Csch[a+b*x]*Csch[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b^2-d^2] && NonzeroQ[b*c-a*d]


Int[u_.*(a_.*Cosh[v_]+b_.*Sinh[v_])^n_.,x_Symbol] :=
  Int[u*(a*E^(a/b*v))^n,x] /;
FreeQ[{a,b,n},x] && ZeroQ[a^2-b^2]



