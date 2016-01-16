(* ::Package:: *)

Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*Cosh[a+b*x]/b - 
  d*m/b*Int[(c+d*x)^(m-1)*Cosh[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Cosh[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*Sinh[a+b*x]/b - 
  d*m/b*Int[(c+d*x)^(m-1)*Sinh[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[Sinh[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  SinhIntegral[b*c/d+b*x]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d]


Int[Cosh[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  CoshIntegral[b*c/d+b*x]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d]


Int[Sinh[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Cosh[(b*c-a*d)/d]*Int[Sinh[b*c/d+b*x]/(c+d*x),x] - 
  Sinh[(b*c-a*d)/d]*Int[Cosh[b*c/d+b*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[Cosh[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Cosh[(b*c-a*d)/d]*Int[Cosh[b*c/d+b*x]/(c+d*x),x] - 
  Sinh[(b*c-a*d)/d]*Int[Sinh[b*c/d+b*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[(c_.+d_.*x_)^m_*Sinh[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Sinh[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Cosh[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1


Int[(c_.+d_.*x_)^m_*Cosh[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Cosh[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Sinh[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_],x_Symbol] :=
  1/2*Int[(c+d*x)^m*E^(a+b*x),x] - 
  1/2*Int[(c+d*x)^m*E^(-a-b*x),x] /;
FreeQ[{a,b,c,d,m},x]


Int[(c_.+d_.*x_)^m_.*Cosh[a_.+b_.*x_],x_Symbol] :=
  1/2*Int[(c+d*x)^m*E^(a+b*x),x] + 
  1/2*Int[(c+d*x)^m*E^(-a-b*x),x] /;
FreeQ[{a,b,c,d,m},x]


Int[(c_.+d_.*x_)*Sinh[a_.+b_.*x_]^n_,x_Symbol] :=
  -d*Sinh[a+b*x]^n/(b^2*n^2) +
  (c+d*x)*Cosh[a+b*x]*Sinh[a+b*x]^(n-1)/(b*n) -
  (n-1)/n*Int[(c+d*x)*Sinh[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1


Int[(c_.+d_.*x_)*Cosh[a_.+b_.*x_]^n_,x_Symbol] :=
  -d*Cosh[a+b*x]^n/(b^2*n^2) +
  (c+d*x)*Sinh[a+b*x]*Cosh[a+b*x]^(n-1)/(b*n) +
  (n-1)/n*Int[(c+d*x)*Cosh[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1


Int[(c_.+d_.*x_)^m_*Sinh[a_.+b_.*x_]^2,x_Symbol] :=
  -d*m*(c+d*x)^(m-1)*Sinh[a+b*x]^2/(4*b^2) + 
  (c+d*x)^m*Cosh[a+b*x]*Sinh[a+b*x]/(2*b) - 
  (c+d*x)^(m+1)/(2*d*(m+1)) + 
  d^2*m*(m-1)/(4*b^2)*Int[(c+d*x)^(m-2)*Sinh[a+b*x]^2,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>1


Int[(c_.+d_.*x_)^m_*Cosh[a_.+b_.*x_]^2,x_Symbol] :=
  -d*m*(c+d*x)^(m-1)*Cosh[a+b*x]^2/(4*b^2) + 
  (c+d*x)^m*Sinh[a+b*x]*Cosh[a+b*x]/(2*b) + 
  (c+d*x)^(m+1)/(2*d*(m+1)) + 
  d^2*m*(m-1)/(4*b^2)*Int[(c+d*x)^(m-2)*Cosh[a+b*x]^2,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>1


Int[(c_.+d_.*x_)^m_*Sinh[a_.+b_.*x_]^n_,x_Symbol] :=
  -d*m*(c+d*x)^(m-1)*Sinh[a+b*x]^n/(b^2*n^2) +
  (c+d*x)^m*Cosh[a+b*x]*Sinh[a+b*x]^(n-1)/(b*n) -
  (n-1)/n*Int[(c+d*x)^m*Sinh[a+b*x]^(n-2),x] +
  d^2*m*(m-1)/(b^2*n^2)*Int[(c+d*x)^(m-2)*Sinh[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m>1 && n!=2


Int[(c_.+d_.*x_)^m_*Cosh[a_.+b_.*x_]^n_,x_Symbol] :=
  -d*m*(c+d*x)^(m-1)*Cosh[a+b*x]^n/(b^2*n^2) +
  (c+d*x)^m*Sinh[a+b*x]*Cosh[a+b*x]^(n-1)/(b*n) +
  (n-1)/n*Int[(c+d*x)^m*Cosh[a+b*x]^(n-2),x] +
  d^2*m*(m-1)/(b^2*n^2)*Int[(c+d*x)^(m-2)*Cosh[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m>1 && n!=2


Int[(c_.+d_.*x_)^m_*Sinh[a_.+b_.*x_]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Sinh[a+b*x]^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && n>1 && (Not[RationalQ[m]] || -1<=m<1)


Int[(c_.+d_.*x_)^m_*Cosh[a_.+b_.*x_]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Cosh[a+b*x]^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && n>1 && (Not[RationalQ[m]] || -1<=m<1)


Int[(c_.+d_.*x_)^m_*Sinh[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Sinh[a+b*x]^n/(d*(m+1)) - 
  b*n/(d*(m+1))*Int[ExpandTrigReduce[(c+d*x)^(m+1),Cosh[a+b*x]*Sinh[a+b*x]^(n-1),x],x] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && n>1 && RationalQ[m] && -2<=m<-1


Int[(c_.+d_.*x_)^m_*Cosh[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Cosh[a+b*x]^n/(d*(m+1)) - 
  b*n/(d*(m+1))*Int[ExpandTrigReduce[(c+d*x)^(m+1),Sinh[a+b*x]*Cosh[a+b*x]^(n-1),x],x] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && n>1 && RationalQ[m] && -2<=m<-1


Int[(c_.+d_.*x_)^m_*Sinh[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Sinh[a+b*x]^n/(d*(m+1)) - 
  b*n*(c+d*x)^(m+2)*Cosh[a+b*x]*Sinh[a+b*x]^(n-1)/(d^2*(m+1)*(m+2)) + 
  b^2*n^2/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*Sinh[a+b*x]^n,x] + 
  b^2*n*(n-1)/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*Sinh[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m<-2


Int[(c_.+d_.*x_)^m_*Cosh[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Cosh[a+b*x]^n/(d*(m+1)) - 
  b*n*(c+d*x)^(m+2)*Sinh[a+b*x]*Cosh[a+b*x]^(n-1)/(d^2*(m+1)*(m+2)) + 
  b^2*n^2/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*Cosh[a+b*x]^n,x] - 
  b^2*n*(n-1)/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*Cosh[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m<-2


Int[(c_.+d_.*x_)*Sinh[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)*Cosh[a+b*x]*Sinh[a+b*x]^(n+1)/(b*(n+1)) -
  d*Sinh[a+b*x]^(n+2)/(b^2*(n+1)*(n+2)) -
  (n+2)/(n+1)*Int[(c+d*x)*Sinh[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1 && n!=-2


Int[(c_.+d_.*x_)*Cosh[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)*Sinh[a+b*x]*Cosh[a+b*x]^(n+1)/(b*(n+1)) +
  d*Cosh[a+b*x]^(n+2)/(b^2*(n+1)*(n+2)) +
  (n+2)/(n+1)*Int[(c+d*x)*Cosh[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1 && n!=-2


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^m*Cosh[a+b*x]*Sinh[a+b*x]^(n+1)/(b*(n+1)) -
  d*m*(c+d*x)^(m-1)*Sinh[a+b*x]^(n+2)/(b^2*(n+1)*(n+2)) -
  (n+2)/(n+1)*Int[(c+d*x)^m*Sinh[a+b*x]^(n+2),x] +
  d^2*m*(m-1)/(b^2*(n+1)*(n+2))*Int[(c+d*x)^(m-2)*Sinh[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n<-1 && n!=-2 && m>1


Int[(c_.+d_.*x_)^m_.*Cosh[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)^m*Sinh[a+b*x]*Cosh[a+b*x]^(n+1)/(b*(n+1)) +
  d*m*(c+d*x)^(m-1)*Cosh[a+b*x]^(n+2)/(b^2*(n+1)*(n+2)) +
  (n+2)/(n+1)*Int[(c+d*x)^m*Cosh[a+b*x]^(n+2),x] -
  d^2*m*(m-1)/(b^2*(n+1)*(n+2))*Int[(c+d*x)^(m-2)*Cosh[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n<-1 && n!=-2 && m>1


Int[(c_.+d_.*x_)^m_.*Tanh[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)/(d*(m+1)) - 
  2*Int[(c+d*x)^m/(1+E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*Coth[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)/(d*(m+1)) - 
  2*Int[(c+d*x)^m/(1-E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*Tanh[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)^m*Tanh[a+b*x]^(n-1)/(b*(n-1)) + 
  d*m/(b*(n-1))*Int[(c+d*x)^(m-1)*Tanh[a+b*x]^(n-1),x] + 
  Int[(c+d*x)^m*Tanh[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m>0


Int[(c_.+d_.*x_)^m_.*Coth[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)^m*Coth[a+b*x]^(n-1)/(b*(n-1)) + 
  d*m/(b*(n-1))*Int[(c+d*x)^(m-1)*Coth[a+b*x]^(n-1),x] + 
  Int[(c+d*x)^m*Coth[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m>0


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


Int[u_^m_.*F_[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F[ExpandToSum[v,x]]^n,x] /;
FreeQ[{m,n},x] && HyperbolicQ[F] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


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


Int[Sinh[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Module[{g=Numerator[1/n]},
  g*Subst[Int[x^(g-1)*Sinh[a+b*x^(n*g)]^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,p},x] && RationalQ[n] && (n<0 || FractionQ[n])


Int[Cosh[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Module[{g=Numerator[1/n]},
  g*Subst[Int[x^(g-1)*Cosh[a+b*x^(n*g)]^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,p},x] && RationalQ[n] && (n<0 || FractionQ[n])


Int[Sinh[a_.+b_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(a+b*x^n),x] - 1/2*Int[E^(-a-b*x^n),x] /;
FreeQ[{a,b,n},x]


Int[Cosh[a_.+b_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(a+b*x^n),x] + 1/2*Int[E^(-a-b*x^n),x] /;
FreeQ[{a,b,n},x]


(* Int[Sinh[a_.+b_.*x_^n_],x_Symbol] :=
  x*Sinh[a+b*x^n] - 
  b*n*Int[x^n*Cosh[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n<0 *)


(* Int[Cosh[a_.+b_.*x_^n_],x_Symbol] :=
  x*Cosh[a+b*x^n] - 
  b*n*Int[x^n*Sinh[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n<0 *)


Int[Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  Int[ExpandTrigReduce[Sinh[a+b*x^n]^p,x],x] /;
FreeQ[{a,b,n},x] && IntegerQ[p] && p>1


Int[Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  Int[ExpandTrigReduce[Cosh[a+b*x^n]^p,x],x] /;
FreeQ[{a,b,n},x] && IntegerQ[p] && p>1


Int[Sinh[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Defer[Int][Sinh[a+b*x^n]^p,x] /;
FreeQ[{a,b,n,p},x]


Int[Cosh[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Defer[Int][Cosh[a+b*x^n]^p,x] /;
FreeQ[{a,b,n,p},x]


Int[Sinh[a_.+b_.*u_^n_]^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[Sinh[a+b*x^n]^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[Cosh[a_.+b_.*u_^n_]^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[Cosh[a+b*x^n]^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[Sinh[b_.*x_^n_]/x_,x_Symbol] :=
  SinhIntegral[b*x^n]/n /;
FreeQ[{b,n},x]


Int[Cosh[b_.*x_^n_]/x_,x_Symbol] :=
  CoshIntegral[b*x^n]/n /;
FreeQ[{b,n},x]


Int[Sinh[a_+b_.*x_^n_]/x_,x_Symbol] :=
  Sinh[a]*Int[Cosh[b*x^n]/x,x] + 
  Cosh[a]*Int[Sinh[b*x^n]/x,x] /;
FreeQ[{a,b,n},x]


Int[Cosh[a_+b_.*x_^n_]/x_,x_Symbol] :=
  Cosh[a]*Int[Cosh[b*x^n]/x,x] + 
  Sinh[a]*Int[Sinh[b*x^n]/x,x] /;
FreeQ[{a,b,n},x]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_],x_Symbol] :=
  Cosh[a+b*x^n]/(b*n) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-(n-1)]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_],x_Symbol] :=
  Sinh[a+b*x^n]/(b*n) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-(n-1)]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m-n+1)*Cosh[a+b*x^n]/(b*n) - 
  (m-n+1)/(b*n)*Int[x^(m-n)*Cosh[a+b*x^n],x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && (0<n<m+1 || m+1<n<0)


Int[x_^m_.*Sinh[a_.+b_.*x_^n_],x_Symbol] :=
  Module[{mn=Simplify[m-n]},
  x^(mn+1)*Cosh[a+b*x^n]/(b*n) - 
  (mn+1)/(b*n)*Int[x^mn*Cosh[a+b*x^n],x]] /;
FreeQ[{a,b,m,n},x] && NonzeroQ[m-n+1] && PositiveIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m-n+1)*Sinh[a+b*x^n]/(b*n) - 
  (m-n+1)/(b*n)*Int[x^(m-n)*Sinh[a+b*x^n],x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && (0<n<m+1 || m+1<n<0)


Int[x_^m_.*Cosh[a_.+b_.*x_^n_],x_Symbol] :=
  Module[{mn=Simplify[m-n]},
  x^(mn+1)*Sinh[a+b*x^n]/(b*n) - 
  (mn+1)/(b*n)*Int[x^mn*Sinh[a+b*x^n],x]] /;
FreeQ[{a,b,m,n},x] && NonzeroQ[m-n+1] && PositiveIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*Sinh[a+b*x^n]/(m+1) - 
  b*n/(m+1)*Int[x^(m+n)*Cosh[a+b*x^n],x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && (n>0 && m<-1 || n<0 && m>-1)


Int[x_^m_.*Sinh[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*Sinh[a+b*x^n]/(m+1) -
  b*n/(m+1)*Int[x^Simplify[m+n]*Cosh[a+b*x^n],x] /;
FreeQ[{a,b,m,n},x] && NegativeIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*Cosh[a+b*x^n]/(m+1) - 
  b*n/(m+1)*Int[x^(m+n)*Sinh[a+b*x^n],x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && (n>0 && m<-1 || n<0 && m>-1)


Int[x_^m_.*Cosh[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*Cosh[a+b*x^n]/(m+1) -
  b*n/(m+1)*Int[x^Simplify[m+n]*Sinh[a+b*x^n],x] /;
FreeQ[{a,b,m,n},x] && NegativeIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_],x_Symbol] :=
  1/2*Int[x^m*E^(a+b*x^n),x] - 1/2*Int[x^m*E^(-a-b*x^n),x] /;
FreeQ[{a,b,m,n},x]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_],x_Symbol] :=
  1/2*Int[x^m*E^(a+b*x^n),x] + 1/2*Int[x^m*E^(-a-b*x^n),x] /;
FreeQ[{a,b,m,n},x]


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


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[Sinh[a+b*x^Simplify[n/(m+1)]]^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[Cosh[a+b*x^Simplify[n/(m+1)]]^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sinh[a+b*x^n]^p,x],x] /;
FreeQ[{a,b,m,n},x] && IntegerQ[p] && p>1 && Not[FractionQ[m]] && Not[FractionQ[n]]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Cosh[a+b*x^n]^p,x],x] /;
FreeQ[{a,b,m,n},x] && IntegerQ[p] && p>1 && Not[FractionQ[m]] && Not[FractionQ[n]]


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


Int[x_^m_.*Sinh[a_.+b_.*u_^n_]^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*Sinh[a+b*x^n]^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && IntegerQ[m] && NonzeroQ[u-x]


Int[x_^m_.*Cosh[a_.+b_.*u_^n_]^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*Cosh[a+b*x^n]^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && IntegerQ[m] && NonzeroQ[u-x]


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


Int[x_^m_.*Tanh[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[Tanh[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-(n-1)]


Int[x_^m_.*Coth[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[Coth[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-(n-1)]


Int[x_^m_.*Tanh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^(m-n+1)*Tanh[a+b*x^n]^(p-1)/(b*n*(p-1)) + 
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Tanh[a+b*x^n]^(p-1),x] + 
  Int[x^m*Tanh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p>1 && 0<n<m+1


Int[x_^m_.*Coth[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^(m-n+1)*Coth[a+b*x^n]^(p-1)/(b*n*(p-1)) + 
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Coth[a+b*x^n]^(p-1),x] + 
  Int[x^m*Coth[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p>1 && 0<n<m+1


Int[x_^m_.*Tanh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m-n+1)*Tanh[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Tanh[a+b*x^n]^(p+1),x] + 
  Int[x^m*Tanh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p<-1 && 0<n<m+1


Int[x_^m_.*Coth[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m-n+1)*Coth[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Coth[a+b*x^n]^(p+1),x] + 
  Int[x^m*Coth[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p<-1 && 0<n<m+1


Int[x_^m_.*Sinh[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[x^m*Sinh[a+b*x]^n*Tanh[a+b*x]^(p-2),x] - Int[x^m*Sinh[a+b*x]^(n-2)*Tanh[a+b*x]^p,x] /;
FreeQ[{a,b,m},x] && PositiveIntegerQ[n,p]


Int[x_^m_.*Cosh[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[x^m*Cosh[a+b*x]^n*Coth[a+b*x]^(p-2),x] + Int[x^m*Cosh[a+b*x]^(n-2)*Coth[a+b*x]^p,x] /;
FreeQ[{a,b,m},x] && PositiveIntegerQ[n,p]


Int[x_^m_.*Sech[a_.+b_.*x_]*Tanh[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[x^m*Sech[a+b*x]*Tanh[a+b*x]^(p-2),x] - Int[x^m*Sech[a+b*x]^3*Tanh[a+b*x]^(p-2),x] /;
FreeQ[{a,b,m},x] && PositiveIntegerQ[p/2]


Int[x_^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[x^m*Sech[a+b*x]^n*Tanh[a+b*x]^(p-2),x] - Int[x^m*Sech[a+b*x]^(n+2)*Tanh[a+b*x]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && PositiveIntegerQ[p/2]


Int[x_^m_.*Csch[a_.+b_.*x_]*Coth[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[x^m*Csch[a+b*x]*Coth[a+b*x]^(p-2),x] + Int[x^m*Csch[a+b*x]^3*Coth[a+b*x]^(p-2),x] /;
FreeQ[{a,b,m},x] && PositiveIntegerQ[p/2]


Int[x_^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[x^m*Csch[a+b*x]^n*Coth[a+b*x]^(p-2),x] + Int[x^m*Csch[a+b*x]^(n+2)*Coth[a+b*x]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && PositiveIntegerQ[p/2]


Int[Sech[a_.+b_.*x_^n_],x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*Sech[a+b*x],x],x,x^n] /;
FreeQ[{a,b},x] && PositiveIntegerQ[1/n]


Int[Csch[a_.+b_.*x_^n_],x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*Csch[a+b*x],x],x,x^n] /;
FreeQ[{a,b},x] && PositiveIntegerQ[1/n]


Int[x_^m_.*Sech[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*Sech[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Csch[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*Csch[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Sech[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Defer[Int][x^m*Sech[a+b*x^n]^p,x] /;
FreeQ[{a,b,m,n,p},x]


Int[x_^m_.*Csch[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Defer[Int][x^m*Csch[a+b*x^n]^p,x] /;
FreeQ[{a,b,m,n,p},x]


Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Sech[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Sech[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]


Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Csch[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Csch[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]


Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_.*Tanh[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
  -x^(m-n+1)*Sech[a+b*x^n]^p/(b*n*p) +
  (m-n+1)/(b*n*p)*Int[x^(m-n)*Sech[a+b*x^n]^p,x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1


Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_.*Coth[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
  -x^(m-n+1)*Csch[a+b*x^n]^p/(b*n*p) +
  (m-n+1)/(b*n*p)*Int[x^(m-n)*Csch[a+b*x^n]^p,x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1


Int[x_^m_.*Csch[a_.+b_.*x_]^n_.*Sech[a_.+b_.*x_]^n_.,x_Symbol] :=
  2^n*Int[x^m*Csch[2*a+2*b*x]^n,x] /;
FreeQ[{a,b},x] && RationalQ[m] && IntegerQ[n]


Int[x_^m_.*Csch[a_.+b_.*x_]^n_.*Sech[a_.+b_.*x_]^p_.,x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[Csch[a+b*x]^n*Sech[a+b*x]^p,x]]},
  Dist[x^m,u,x] - 
  m*Int[x^(m-1)*u,x]] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && RationalQ[m] && m>0 && n!=p


Int[F_[v_]^p_.,x_Symbol] :=
  Int[F[ExpandToSum[v,x]]^p,x] /;
FreeQ[p,x] && HyperbolicQ[F] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[x_^m_.*F_[v_]^p_.,x_Symbol] :=
  Int[x^m*F[ExpandToSum[v,x]]^p,x] /;
FreeQ[{m,p},x] && HyperbolicQ[F] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[(c_.*Sinh[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Sinh[a+b*x^n]^p]/Sinh[a+b*x^n]^(p/2)*Int[Sinh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[(c_.*Cosh[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Cosh[a+b*x^n]^p]/Cosh[a+b*x^n]^(p/2)*Int[Cosh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[(c_.*Sinh[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Sinh[a+b*x^n]^(p/2)/Sqrt[c*Sinh[a+b*x^n]^p]*Int[Sinh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[(c_.*Cosh[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Cosh[a+b*x^n]^(p/2)/Sqrt[c*Cosh[a+b*x^n]^p]*Int[Cosh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[(c_.*Sinh[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  (c*Sinh[a+b*x^n]^p)^q/Sinh[a+b*x^n]^(p*q)*Int[Sinh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[(c_.*Cosh[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  (c*Cosh[a+b*x^n]^p)^q/Cosh[a+b*x^n]^(p*q)*Int[Cosh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sinh[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Sinh[a+b*x^n]^p]/Sinh[a+b*x^n]^(p/2)*Int[x^m*Sinh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Cosh[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Cosh[a+b*x^n]^p]/Cosh[a+b*x^n]^(p/2)*Int[x^m*Cosh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sinh[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Sinh[a+b*x^n]^(p/2)/Sqrt[c*Sinh[a+b*x^n]^p]*Int[x^m*Sinh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Cosh[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Cosh[a+b*x^n]^(p/2)/Sqrt[c*Cosh[a+b*x^n]^p]*Int[x^m*Cosh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sinh[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  (c*Sinh[a+b*x^n]^p)^q/Sinh[a+b*x^n]^(p*q)*Int[x^m*Sinh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Cosh[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  (c*Cosh[a+b*x^n]^p)^q/Cosh[a+b*x^n]^(p*q)*Int[x^m*Cosh[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[(c_.*Sech[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Sech[a+b*x^n]^p]/Sech[a+b*x^n]^(p/2)*Int[Sech[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[(c_.*Csch[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Csch[a+b*x^n]^p]/Csch[a+b*x^n]^(p/2)*Int[Csch[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[(c_.*Sech[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Sech[a+b*x^n]^(p/2)/Sqrt[c*Sech[a+b*x^n]^p]*Int[Sech[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[(c_.*Csch[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Csch[a+b*x^n]^(p/2)/Sqrt[c*Csch[a+b*x^n]^p]*Int[Csch[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[(c_.*Sech[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  (c*Sech[a+b*x^n]^p)^q/Sech[a+b*x^n]^(p*q)*Int[Sech[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[(c_.*Csch[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  (c*Csch[a+b*x^n]^p)^q/Csch[a+b*x^n]^(p*q)*Int[Csch[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sech[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Sech[a+b*x^n]^p]/Sech[a+b*x^n]^(p/2)*Int[x^m*Sech[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Csch[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Csch[a+b*x^n]^p]/Csch[a+b*x^n]^(p/2)*Int[x^m*Csch[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sech[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Sech[a+b*x^n]^(p/2)/Sqrt[c*Sech[a+b*x^n]^p]*Int[x^m*Sech[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && NegativeIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Csch[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Csch[a+b*x^n]^(p/2)/Sqrt[c*Csch[a+b*x^n]^p]*Int[x^m*Csch[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && NegativeIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sech[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  (c*Sech[a+b*x^n]^p)^q/Sech[a+b*x^n]^(p*q)*Int[x^m*Sech[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Csch[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  (c*Csch[a+b*x^n]^p)^q/Csch[a+b*x^n]^(p*q)*Int[x^m*Csch[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[(c_.*F_[v_]^p_.)^q_,x_Symbol] :=
  Int[(c*F[ExpandToSum[v,x]]^p)^q,x] /;
FreeQ[{c,p,q},x] && HyperbolicQ[F] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[x_^m_.*(c_.*F_[v_]^p_.)^q_,x_Symbol] :=
  Int[x^m*(c*F[ExpandToSum[v,x]]^p)^q,x] /;
FreeQ[{c,m,p,q},x] && HyperbolicQ[F] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


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


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^n*Int[(e+f*x)^m*Cosh[-Pi*a/(4*b)+c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2+b^2] && IntegerQ[n]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^n*Int[(e+f*x)^m*Cosh[c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a-b] && IntegerQ[n]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (-2*a)^n*Int[(e+f*x)^m*Sinh[c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a+b] && IntegerQ[n]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^(n-1/2)*Sqrt[a+b*Sinh[c+d*x]]/Cosh[-Pi*a/(4*b)+c/2+d*x/2]*
    Int[(e+f*x)^m*Cosh[-Pi*a/(4*b)+c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^(n-1/2)*Sqrt[a+b*Cosh[c+d*x]]/Cosh[c/2+d*x/2]*Int[(e+f*x)^m*Cosh[c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a-b] && Not[IntegerQ[n]]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (-2*a)^(n-1/2)*Sqrt[a+b*Cosh[c+d*x]]/Sinh[c/2+d*x/2]*Int[(e+f*x)^m*Sinh[c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a+b] && Not[IntegerQ[n]]


Int[x_/(a_+b_.*Sinh[c_.+d_.*x_])^2,x_Symbol] :=
  a/(a^2+b^2)*Int[x/(a+b*Sinh[c+d*x]),x] +
  b/(a^2+b^2)*Int[x*(b-a*Sinh[c+d*x])/(a+b*Sinh[c+d*x])^2,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[x_/(a_+b_.*Cosh[c_.+d_.*x_])^2,x_Symbol] :=
  a/(a^2-b^2)*Int[x/(a+b*Cosh[c+d*x]),x] -
  b/(a^2-b^2)*Int[x*(b+a*Cosh[c+d*x])/(a+b*Cosh[c+d*x])^2,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2^n*Int[x^m*(-b+2*a*E^(c+d*x)+b*E^(2*(c+d*x)))^n/E^(n*(c+d*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0 && IntegerQ[n] && n<0


Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2^n*Int[x^m*(b+2*a*E^(c+d*x)+b*E^(2*(c+d*x)))^n/E^(n*(c+d*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[n] && n<0


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sinh[c_.+d_.*x_]*Cosh[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(e+f*x)^m*(a+b*Sinh[2*c+2*d*x]/2)^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a-b+b*Cosh[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b] && IntegersQ[m,n] && m>0 && n<0 && (n==-1 || m==1 && n==-2)


Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a+b+b*Cosh[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b] && IntegersQ[m,n] && m>0 && n<0 && (n==-1 || m==1 && n==-2)


Int[(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*Sinh[c+d*x]/(d^2-b^2*p^2*Log[f]^2) + 
  d*(f^(a+b*x))^p*Cosh[c+d*x]/(d^2-b^2*p^2*Log[f]^2) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2-b^2*p^2*Log[f]^2]


Int[(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*Cosh[c+d*x]/(d^2-b^2*p^2*Log[f]^2) + 
  d*(f^(a+b*x))^p*Sinh[c+d*x]/(d^2-b^2*p^2*Log[f]^2) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2-b^2*p^2*Log[f]^2]


Int[(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^n_,x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*Sinh[c+d*x]^n/(d^2*n^2-b^2*p^2*Log[f]^2) + 
  d*n*(f^(a+b*x))^p*Cosh[c+d*x]*Sinh[c+d*x]^(n-1)/(d^2*n^2-b^2*p^2*Log[f]^2) - 
  n*(n-1)*d^2/(d^2*n^2-b^2*p^2*Log[f]^2)*Int[(f^(a+b*x))^p*Sinh[c+d*x]^(n-2),x] /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*n^2-b^2*p^2*Log[f]^2] && RationalQ[n] && n>1


Int[(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_]^n_,x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*Cosh[c+d*x]^n/(d^2*n^2-b^2*p^2*Log[f]^2) + 
  d*n*(f^(a+b*x))^p*Sinh[c+d*x]*Cosh[c+d*x]^(n-1)/(d^2*n^2-b^2*p^2*Log[f]^2) + 
  n*(n-1)*d^2/(d^2*n^2-b^2*p^2*Log[f]^2)*Int[(f^(a+b*x))^p*Cosh[c+d*x]^(n-2),x] /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*n^2-b^2*p^2*Log[f]^2] && RationalQ[n] && n>1


Int[(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^n_,x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*Sinh[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) + 
  (f^(a+b*x))^p*Cosh[c+d*x]*Sinh[c+d*x]^(n+1)/(d*(n+1)) /;
FreeQ[{a,b,c,d,f,n,p},x] && ZeroQ[d^2*(n+2)^2-b^2*p^2*Log[f]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]


Int[(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_]^n_,x_Symbol] :=
  b*p*Log[f]*(f^(a+b*x))^p*Cosh[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) - 
  (f^(a+b*x))^p*Sinh[c+d*x]*Cosh[c+d*x]^(n+1)/(d*(n+1)) /;
FreeQ[{a,b,c,d,f,n,p},x] && ZeroQ[d^2*(n+2)^2-b^2*p^2*Log[f]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]


Int[(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^n_,x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*Sinh[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) + 
  (f^(a+b*x))^p*Cosh[c+d*x]*Sinh[c+d*x]^(n+1)/(d*(n+1)) - 
  (d^2*(n+2)^2-b^2*p^2*Log[f]^2)/(d^2*(n+1)*(n+2))*Int[(f^(a+b*x))^p*Sinh[c+d*x]^(n+2),x] /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*(n+2)^2-b^2*p^2*Log[f]^2] && RationalQ[n] && n<-1 && n!=-2


Int[(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_]^n_,x_Symbol] :=
  b*p*Log[f]*(f^(a+b*x))^p*Cosh[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) - 
  (f^(a+b*x))^p*Sinh[c+d*x]*Cosh[c+d*x]^(n+1)/(d*(n+1)) + 
  (d^2*(n+2)^2-b^2*p^2*Log[f]^2)/(d^2*(n+1)*(n+2))*Int[(f^(a+b*x))^p*Cosh[c+d*x]^(n+2),x] /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*(n+2)^2-b^2*p^2*Log[f]^2] && RationalQ[n] && n<-1 && n!=-2


Int[(f_^(a_.+b_.*x_))^p_.*Sech[c_.+d_.*x_]^n_,x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*(Sech[c+d*x]^n/(d^2*n^2-b^2*p^2*Log[f]^2)) - 
  d*n*(f^(a+b*x))^p*Sech[c+d*x]^(n+1)*(Sinh[c+d*x]/(d^2*n^2-b^2*p^2*Log[f]^2)) + 
  d^2*n*((n+1)/(d^2*n^2-b^2*p^2*Log[f]^2))*Int[(f^(a+b*x))^p*Sech[c+d*x]^(n+2),x] /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*n^2+b^2*p^2*Log[f]^2] && RationalQ[n] && n<-1


Int[(f_^(a_.+b_.*x_))^p_.*Csch[c_.+d_.*x_]^n_,x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*(Csch[c+d*x]^n/(d^2*n^2-b^2*p^2*Log[f]^2)) - 
  d*n*(f^(a+b*x))^p*Csch[c+d*x]^(n+1)*(Cosh[c+d*x]/(d^2*n^2-b^2*p^2*Log[f]^2)) - 
  d^2*n*((n+1)/(d^2*n^2-b^2*p^2*Log[f]^2))*Int[(f^(a+b*x))^p*Csch[c+d*x]^(n+2),x] /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*n^2+b^2*p^2*Log[f]^2] && RationalQ[n] && n<-1


Int[(f_^(a_.+b_.*x_))^p_.*Sech[c_.+d_.*x_]^n_,x_Symbol] :=
  b*p*Log[f]*(f^(a+b*x))^p*Sech[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) + 
  (f^(a+b*x))^p*Sech[c+d*x]^(n-1)*Sinh[c+d*x]/(d*(n-1)) /;
FreeQ[{a,b,c,d,f,p,n},x] && ZeroQ[b^2*p^2*Log[f]^2-d^2*(n-2)^2] && NonzeroQ[n-1] && NonzeroQ[n-2]


Int[(f_^(a_.+b_.*x_))^p_.*Csch[c_.+d_.*x_]^n_,x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*Csch[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) - 
  (f^(a+b*x))^p*Csch[c+d*x]^(n-1)*Cosh[c+d*x]/(d*(n-1)) /;
FreeQ[{a,b,c,d,f,p,n},x] && ZeroQ[b^2*p^2*Log[f]^2-d^2*(n-2)^2] && NonzeroQ[n-1] && NonzeroQ[n-2]


Int[(f_^(a_.+b_.*x_))^p_.*Sech[c_.+d_.*x_]^n_,x_Symbol] :=
  b*p*Log[f]*(f^(a+b*x))^p*Sech[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) + 
  (f^(a+b*x))^p*Sech[c+d*x]^(n-1)*Sinh[c+d*x]/(d*(n-1)) -
  (b^2*p^2*Log[f]^2-d^2*(n-2)^2)/(d^2*(n-1)*(n-2))*Int[(f^(a+b*x))^p*Sech[c+d*x]^(n-2),x] /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[b^2*p^2*Log[f]^2-d^2*(n-2)^2] && 
  RationalQ[n] && n>1 && n!=2


Int[(f_^(a_.+b_.*x_))^p_.*Csch[c_.+d_.*x_]^n_,x_Symbol] :=
  -b*p*Log[f]*(f^(a+b*x))^p*Csch[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) - 
  (f^(a+b*x))^p*Csch[c+d*x]^(n-1)*Cosh[c+d*x]/(d*(n-1)) +
  (b^2*p^2*Log[f]^2-d^2*(n-2)^2)/(d^2*(n-1)*(n-2))*Int[(f^(a+b*x))^p*Csch[c+d*x]^(n-2),x] /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[b^2*p^2*Log[f]^2-d^2*(n-2)^2] && 
  RationalQ[n] && n>1 && n!=2


Int[(f_^(a_.+b_.*x_))^p_.*F_[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[(f^(a+b*x))^p,F[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d,f,n,p},x] && HyperbolicQ[F]


Int[(f_^u_)^p_.*F_[v_]^n_.,x_Symbol] :=
  Int[(f^ExpandToSum[u,x])^p*F[ExpandToSum[v,x]]^n,x] /;
FreeQ[{n,p},x] && HyperbolicQ[F] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[x_^m_.*(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^n_.,x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(f^(a+b*x))^p*Sinh[c+d*x]^n,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]] /;
FreeQ[{a,b,c,d,f,p},x] && RationalQ[m] && m>0 && IntegerQ[n] && n>0


Int[x_^m_.*(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_]^n_.,x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(f^(a+b*x))^p*Cosh[c+d*x]^n,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]] /;
FreeQ[{a,b,c,d,f,p},x] && RationalQ[m] && m>0 && IntegerQ[n] && n>0


Int[(F_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^m_.*Cosh[e_.+f_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[(F^(a+b*x))^p,Sinh[c+d*x]^m*Cosh[e+f*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,p},x] && PositiveIntegerQ[m,n]


Int[x_^q_.*(F_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^m_.*Cosh[e_.+f_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^q*(F^(a+b*x))^p,Sinh[c+d*x]^m*Cosh[e+f*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,p},x] && PositiveIntegerQ[m,n,q]


Int[f_^(c_.*(a_.+b_.*x_))*F_[d_.+e_.*x_]^m_.*G_[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[f^(c*(a+b*x)),F[d+e*x]^m*G[d+e*x]^n,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m,n] && HyperbolicQ[F] && HyperbolicQ[G]


Int[f_^u_*Sinh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[f^u,Sinh[v]^n,x],x] /;
FreeQ[f,x] && (LinearQ[u,x] || QuadraticQ[u,x]) && (LinearQ[v,x] || QuadraticQ[v,x]) && PositiveIntegerQ[n]


Int[f_^u_*Cosh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[f^u,Cosh[v]^n,x],x] /;
FreeQ[f,x] && (LinearQ[u,x] || QuadraticQ[u,x]) && (LinearQ[v,x] || QuadraticQ[v,x]) && PositiveIntegerQ[n]


Int[f_^u_*Sinh[v_]^m_.*Cosh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[f^u,Sinh[v]^m*Cosh[v]^n,x],x] /;
FreeQ[f,x] && (LinearQ[u,x] || QuadraticQ[u,x]) && (LinearQ[v,x] || QuadraticQ[v,x]) && PositiveIntegerQ[m,n]


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
  Int[(2/((c*x^n)^b+1/(c*x^n)^b))^p,x] /;
FreeQ[c,x] && RationalQ[b,n,p]


Int[Csch[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[(2/((c*x^n)^b - 1/(c*x^n)^b))^p,x] /;
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


Int[x_^m_.Sech[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[x^m*(2/((c*x^n)^b+1/(c*x^n)^b))^p,x] /;
FreeQ[c,x] && RationalQ[b,m,n,p]


Int[x_^m_.*Csch[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[x^m*(2/((c*x^n)^b - 1/(c*x^n)^b))^p,x] /;
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
  Module[{lst=QuotientOfLinearsParts[u,x]},
  Int[Sinh[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
PositiveIntegerQ[n] && QuotientOfLinearsQ[u,x]


Int[Cosh[u_]^n_.,x_Symbol] :=
  Module[{lst=QuotientOfLinearsParts[u,x]},
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


Int[x_^m_.*Sinh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d*Subst[Int[(-c/d+x/d)^m*Sinh[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && RationalQ[p]


Int[x_^m_.*Cosh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d*Subst[Int[(-c/d+x/d)^m*Cosh[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && RationalQ[p]


Int[x_^m_./(a_.+b_.*Cosh[d_.+e_.*x_]^2+c_.*Sinh[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[x^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[m] && NonzeroQ[a+b] && NonzeroQ[a+c]


Int[x_*(A_+B_.*Sinh[c_.+d_.*x_])/(a_+b_.*Sinh[c_.+d_.*x_])^2,x_Symbol] :=
  B*x*Cosh[c+d*x]/(a*d*(a+b*Sinh[c+d*x])) - 
  B/(a*d)*Int[Cosh[c+d*x]/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a*A+b*B]


Int[x_*(A_+B_.*Cosh[c_.+d_.*x_])/(a_+b_.*Cosh[c_.+d_.*x_])^2,x_Symbol] :=
  B*x*Sinh[c+d*x]/(a*d*(a+b*Cosh[c+d*x])) -
  B/(a*d)*Int[Sinh[c+d*x]/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a*A-b*B]


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


Int[ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tanh[a+b*x]] - 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2+1]


Int[ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tanh[a+b*x]] + 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2+1]


Int[ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tanh[a+b*x]] - 
  I*b*(-I+c-d)*Int[x/(-I+c-d+(-I+c+d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c-d)*Int[x/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2+1]


Int[ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tanh[a+b*x]] + 
  I*b*(-I+c-d)*Int[x/(-I+c-d+(-I+c+d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c-d)*Int[x/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2+1]


Int[x_^m_.*ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTan[c+d*Tanh[a+b*x]]/(m+1) - 
  b/(m+1)*Int[x^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCot[c+d*Tanh[a+b*x]]/(m+1) + 
  b/(m+1)*Int[x^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTan[c+d*Tanh[a+b*x]]/(m+1) - 
  I*b*(-I+c-d)/(m+1)*Int[x^(m+1)/(-I+c-d+(-I+c+d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c-d)/(m+1)*Int[x^(m+1)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCot[c+d*Tanh[a+b*x]]/(m+1) + 
  I*b*(-I+c-d)/(m+1)*Int[x^(m+1)/(-I+c-d+(-I+c+d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c-d)/(m+1)*Int[x^(m+1)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2+1] && RationalQ[m] && m>0


Int[ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Coth[a+b*x]] - 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2+1]


Int[ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Coth[a+b*x]] + 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2+1]


Int[ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Coth[a+b*x]] - 
  I*b*(-I+c-d)*Int[x/(-I+c-d-(-I+c+d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c-d)*Int[x/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2+1]


Int[ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Coth[a+b*x]] + 
  I*b*(-I+c-d)*Int[x/(-I+c-d-(-I+c+d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c-d)*Int[x/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2+1]


Int[x_^m_.*ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTan[c+d*Coth[a+b*x]]/(m+1) - 
  b/(m+1)*Int[x^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCot[c+d*Coth[a+b*x]]/(m+1) + 
  b/(m+1)*Int[x^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTan[c+d*Coth[a+b*x]]/(m+1) - 
  I*b*(-I+c-d)/(m+1)*Int[x^(m+1)/(-I+c-d-(-I+c+d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c-d)/(m+1)*Int[x^(m+1)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCot[c+d*Coth[a+b*x]]/(m+1) + 
  I*b*(-I+c-d)/(m+1)*Int[x^(m+1)/(-I+c-d-(-I+c+d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c-d)/(m+1)*Int[x^(m+1)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2+1] && RationalQ[m] && m>0


Int[ArcTanh[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Tanh[a+b*x]] + 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2-1]


Int[ArcCoth[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Tanh[a+b*x]] + 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2-1]


Int[ArcTanh[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Tanh[a+b*x]] + 
  b*(1+c-d)*Int[x/(1+c-d+(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c+d)*Int[x/(1-c+d+(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2-1]


Int[ArcCoth[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Tanh[a+b*x]] + 
  b*(1+c-d)*Int[x/(1+c-d+(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c+d)*Int[x/(1-c+d+(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2-1]


Int[x_^m_.*ArcTanh[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTanh[c+d*Tanh[a+b*x]]/(m+1) + 
  b/(m+1)*Int[x^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCoth[c+d*Tanh[a+b*x]]/(m+1) + 
  b/(m+1)*Int[x^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcTanh[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTanh[c+d*Tanh[a+b*x]]/(m+1) + 
  b*(1+c-d)/(m+1)*Int[x^(m+1)/(1+c-d+(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c+d)/(m+1)*Int[x^(m+1)/(1-c+d+(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCoth[c+d*Tanh[a+b*x]]/(m+1) + 
  b*(1+c-d)/(m+1)*Int[x^(m+1)/(1+c-d+(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c+d)/(m+1)*Int[x^(m+1)/(1-c+d+(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2-1] && RationalQ[m] && m>0


Int[ArcTanh[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Coth[a+b*x]] + 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2-1]


Int[ArcCoth[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Coth[a+b*x]] + 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2-1]


Int[ArcTanh[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Coth[a+b*x]] + 
  b*(1+c-d)*Int[x/(1+c-d-(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c+d)*Int[x/(1-c+d-(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2-1]


Int[ArcCoth[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Coth[a+b*x]] + 
  b*(1+c-d)*Int[x/(1+c-d-(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c+d)*Int[x/(1-c+d-(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2-1]


Int[x_^m_.*ArcTanh[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTanh[c+d*Coth[a+b*x]]/(m+1) + 
  b/(m+1)*Int[x^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCoth[c+d*Coth[a+b*x]]/(m+1) + 
  b/(m+1)*Int[x^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcTanh[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTanh[c+d*Coth[a+b*x]]/(m+1) + 
  b*(1+c-d)/(m+1)*Int[x^(m+1)/(1+c-d-(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c+d)/(m+1)*Int[x^(m+1)/(1-c+d-(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCoth[c+d*Coth[a+b*x]]/(m+1) + 
  b*(1+c-d)/(m+1)*Int[x^(m+1)/(1+c-d-(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c+d)/(m+1)*Int[x^(m+1)/(1-c+d-(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-d)^2-1] && RationalQ[m] && m>0
