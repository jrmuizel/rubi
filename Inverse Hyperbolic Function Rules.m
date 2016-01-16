(* ::Package:: *)

Int[ArcSinh[c_.+d_.*x_],x_Symbol] :=
  (c+d*x)*ArcSinh[c+d*x]/d - Sqrt[1+(c+d*x)^2]/d /;
FreeQ[{c,d},x]


Int[ArcCosh[c_.+d_.*x_],x_Symbol] :=
  (c+d*x)*ArcCosh[c+d*x]/d - Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]/d /;
FreeQ[{c,d},x]


Int[(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcSinh[c+d*x])^n/d - 
  b*n*Int[(c+d*x)*(a+b*ArcSinh[c+d*x])^(n-1)/Sqrt[1+(c+d*x)^2],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && 0<n<1


Int[(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcCosh[c+d*x])^n/d - 
  b*n*Int[(c+d*x)*(a+b*ArcCosh[c+d*x])^(n-1)/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && 0<n<1


Int[(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcSinh[c+d*x])^n/d - 
  b*n*Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])^(n-1)/d + 
  b^2*n*(n-1)*Int[(a+b*ArcSinh[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1


Int[(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcCosh[c+d*x])^n/d - 
  b*n*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])^(n-1)/d + 
  b^2*n*(n-1)*Int[(a+b*ArcCosh[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1


Int[1/(a_.+b_.*ArcSinh[c_.+d_.*x_])^2,x_Symbol] :=
  -Sqrt[1+(c+d*x)^2]/(b*d*(a+b*ArcSinh[c+d*x])) + 
  1/b*Int[(c+d*x)/(Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(a_.+b_.*ArcCosh[c_.+d_.*x_])^2,x_Symbol] :=
  -Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]/(b*d*(a+b*ArcCosh[c+d*x])) + 
  1/b*Int[(c+d*x)/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(a_.+b_.*ArcSinh[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*Sqrt[1+(c+d*x)^2]/(b*d*Sqrt[a+b*ArcSinh[c+d*x]]) + 
  2/b*Int[(c+d*x)/(Sqrt[1+(c+d*x)^2]*Sqrt[a+b*ArcSinh[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(a_.+b_.*ArcCosh[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]/(b*d*Sqrt[a+b*ArcCosh[c+d*x]]) + 
  2/b*Int[(c+d*x)/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*Sqrt[a+b*ArcCosh[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x]


Int[(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  -(c+d*x)*(a+b*ArcSinh[c+d*x])^(n+2)/(b^2*d*(n+1)*(n+2)) + 
  Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])^(n+1)/(b*d*(n+1)) + 
  1/(b^2*(n+1)*(n+2))*Int[(a+b*ArcSinh[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-2


Int[(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  -(c+d*x)*(a+b*ArcCosh[c+d*x])^(n+2)/(b^2*d*(n+1)*(n+2)) + 
  Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])^(n+1)/(b*d*(n+1)) + 
  1/(b^2*(n+1)*(n+2))*Int[(a+b*ArcCosh[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-2


Int[(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(b*d)*Subst[Int[x^n*Cosh[a/b-x/b],x],x,a+b*ArcSinh[c+d*x]] /;
FreeQ[{a,b,c,d,n},x]


Int[(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  -1/(b*d)*Subst[Int[x^n*Sinh[a/b-x/b],x],x,a+b*ArcCosh[c+d*x]] /;
FreeQ[{a,b,c,d,n},x]


Int[(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_./(e_.+f_.*x_),x_Symbol] :=
  1/f*Subst[Int[(a+b*x)^n*Coth[x],x],x,ArcSinh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_./(e_.+f_.*x_),x_Symbol] :=
  1/f*Subst[Int[(a+b*x)^n*Tanh[x],x],x,ArcCosh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_/(e_.+f_.*x_),x_Symbol] :=
  Defer[Int][(a+b*ArcSinh[c+d*x])^n/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && (NonzeroQ[d*e-c*f] || Not[PositiveIntegerQ[n]])


Int[(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_/(e_.+f_.*x_),x_Symbol] :=
  Defer[Int][(a+b*ArcCosh[c+d*x])^n/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && (NonzeroQ[d*e-c*f] || Not[PositiveIntegerQ[n]])


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcSinh[c_.+d_.*x_]),x_Symbol] :=
  f^m/(b*d^(m+1))*Subst[Int[(Sinh[x/b-a/b]^m*Cosh[x/b-a/b])/x,x],x,a+b*ArcSinh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcCosh[c_.+d_.*x_]),x_Symbol] :=
  f^m/(b*d^(m+1))*Subst[Int[(Cosh[x/b-a/b]^m*Sinh[x/b-a/b])/x,x],x,a+b*ArcCosh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcSinh[c_.+d_.*x_])^2,x_Symbol] :=
  -(e+f*x)^m*Sqrt[1+(c+d*x)^2]/(b*d*(a+b*ArcSinh[c+d*x])) + 
  f^m/(b^2*d^(m+1))*Subst[Int[Expand[TrigReduce[Sinh[x/b-a/b]^(m-1)*(m+(m+1)*Sinh[x/b-a/b]^2)]/x],x],x,a+b*ArcSinh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcCosh[c_.+d_.*x_])^2,x_Symbol] :=
  -(e+f*x)^m*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]/(b*d*(a+b*ArcCosh[c+d*x])) - 
  f^m/(b^2*d^(m+1))*Subst[Int[Expand[TrigReduce[Cosh[x/b-a/b]^(m-1)*(m-(m+1)*Cosh[x/b-a/b]^2)]/x],x],x,a+b*ArcCosh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcSinh[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*(e+f*x)^m*Sqrt[1+(c+d*x)^2]/(b*d*Sqrt[a+b*ArcSinh[c+d*x]]) + 
  4*f^m/(b^2*d^(m+1))*Subst[Int[TrigReduce[Sinh[x^2/b-a/b]^(m-1)*(m+(m+1)*Sinh[x^2/b-a/b]^2)],x],x,Sqrt[a+b*ArcSinh[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcCosh[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*(e+f*x)^m*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]/(b*d*Sqrt[a+b*ArcCosh[c+d*x]]) - 
  4*f^m/(b^2*d^(m+1))*Subst[Int[TrigReduce[Cosh[x^2/b-a/b]^(m-1)*(m-(m+1)*Cosh[x^2/b-a/b]^2)],x],x,Sqrt[a+b*ArcCosh[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)*Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*(a+b*ArcSinh[c+d*x])^(n+2)/(d^2*b^2*(n+1)*(n+2)) - 
  2*d/(b*f*(n+1))*Int[(e+f*x)^2*(a+b*ArcSinh[c+d*x])^(n+1)/Sqrt[1+(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && RationalQ[n] && n<-1 && n!=-2


Int[(e_.+f_.*x_)*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*(a+b*ArcCosh[c+d*x])^(n+2)/(d^2*b^2*(n+1)*(n+2)) - 
  2*d/(b*f*(n+1))*Int[(e+f*x)^2*(a+b*ArcCosh[c+d*x])^(n+1)/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && RationalQ[n] && n<-1 && n!=-2


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)^m*Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m*(e+f*x)^(m-1)*(a+b*ArcSinh[c+d*x])^(n+2)/(b^2*d^2*(n+1)*(n+2)) - 
  (m+1)*(e+f*x)^(m+1)*(a+b*ArcSinh[c+d*x])^(n+2)/(b^2*f*(n+1)*(n+2))  + 
  (m+1)^2/(b^2*(n+1)*(n+2))*Int[(e+f*x)^m*(a+b*ArcSinh[c+d*x])^(n+2),x] + 
  f^2*m*(m-1)/(b^2*d^2*(n+1)*(n+2))*Int[(e+f*x)^(m-2)*(a+b*ArcSinh[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && RationalQ[n] && n<-2 && IntegerQ[m] && m>1


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)^m*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m*(e+f*x)^(m-1)*(a+b*ArcCosh[c+d*x])^(n+2)/(b^2*d^2*(n+1)*(n+2)) - 
  (m+1)*(e+f*x)^(m+1)*(a+b*ArcCosh[c+d*x])^(n+2)/(b^2*f*(n+1)*(n+2)) + 
  (m+1)^2/(b^2*(n+1)*(n+2))*Int[(e+f*x)^m*(a+b*ArcCosh[c+d*x])^(n+2),x] - 
  f^2*m*(m-1)/(b^2*d^2*(n+1)*(n+2))*Int[(e+f*x)^(m-2)*(a+b*ArcCosh[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && RationalQ[n] && n<-2 && IntegerQ[m] && m>1


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcSinh[c+d*x])^n/(f*(m+1)) - 
  b*d*n/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcSinh[c+d*x])^(n-1)/Sqrt[1+(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[m+1] && ZeroQ[d*e-c*f] && Not[RationalQ[n] && n<0] && 
  (RationalQ[n] && n>0 || PositiveIntegerQ[m])


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcCosh[c+d*x])^n/(f*(m+1)) - 
  b*d*n/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcCosh[c+d*x])^(n-1)/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[m+1] && ZeroQ[d*e-c*f] && Not[RationalQ[n] && n<0] && 
  (RationalQ[n] && n>0 || PositiveIntegerQ[m])


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_]),x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcSinh[c+d*x])/(f*(m+1)) - 
  b*d/(f*(m+1))*Int[(e+f*x)^(m+1)/Sqrt[1+(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[d*e-c*f] && NonzeroQ[m+1]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_]),x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcCosh[c+d*x])/(f*(m+1)) - 
  b*d/(f*(m+1))*Int[(e+f*x)^(m+1)/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[d*e-c*f] && NonzeroQ[m+1]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcSinh[c+d*x])^n/(f*(m+1)) - 
  b*d*n/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcSinh[c+d*x])^(n-1)/Sqrt[1+(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m<-1


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcCosh[c+d*x])^n/(f*(m+1)) - 
  b*d*n/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcCosh[c+d*x])^(n-1)/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m<-1


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+b*ArcSinh[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[d*e-c*f] && PositiveIntegerQ[m] && NonzeroQ[c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+b*ArcCosh[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[d*e-c*f] && PositiveIntegerQ[m] && NonzeroQ[c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/(b*d^(m+1))*Subst[Int[x^n*Cosh[x/b-a/b]*(d*e-c*f+f*Sinh[x/b-a/b])^m,x],x,a+b*ArcSinh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && IntegerQ[m] && IntegerQ[n] && Not[m<0 && n<0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/(b*d^(m+1))*Subst[Int[x^n*Sinh[x/b-a/b]*(d*e-c*f+f*Cosh[x/b-a/b])^m,x],x,a+b*ArcCosh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && IntegerQ[m] && IntegerQ[n] && Not[m<0 && n<0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
  2/(b*d^(m+1))*Subst[Int[x^(2*n+1)*Cosh[x^2/b-a/b]*(d*e-c*f+f*Sinh[x^2/b-a/b])^m,x],x,Sqrt[a+b*ArcSinh[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n-1/2]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
  2/(b*d^(m+1))*Subst[Int[x^(2*n+1)*Sinh[x^2/b-a/b]*(d*e-c*f+f*Cosh[x^2/b-a/b])^m,x],x,Sqrt[a+b*ArcCosh[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n-1/2]


Int[1/(Sqrt[u_]*(a_.+b_.*ArcSinh[c_.+d_.*x_])),x_Symbol] :=
  Log[a+b*ArcSinh[c+d*x]]/(b*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[u-(1+(c+d*x)^2)]


Int[(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  (a+b*ArcSinh[c+d*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[u-(1+(c+d*x)^2)] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  f*Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])^n/d^2 - 
  b*f*n/d*Int[(a+b*ArcSinh[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[n] && n>0


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  f*(e+f*x)^(m-1)*Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])^n/(d^2*m) - 
  b*f*n/(d*m)*Int[(e+f*x)^(m-1)*(a+b*ArcSinh[c+d*x])^(n-1),x] - 
  f^2*(m-1)/(d^2*m)*Int[(e+f*x)^(m-2)*(a+b*ArcSinh[c+d*x])^n/Sqrt[1+(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m>1


Int[ArcSinh[c_.+d_.*x_]/((e_.+f_.*x_)*Sqrt[u_]),x_Symbol] :=
  2*ArcTanh[c+d*x-Sqrt[1+(c+d*x)^2]]*ArcSinh[c+d*x]/f + 
  PolyLog[2,c+d*x-Sqrt[1+(c+d*x)^2]]/f - 
  PolyLog[2,-c-d*x+Sqrt[1+(c+d*x)^2]]/f /;
FreeQ[{c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && ZeroQ[d*e-c*f]


Int[(a_+b_.*ArcSinh[c_.+d_.*x_])/((e_.+f_.*x_)*Sqrt[u_]),x_Symbol] :=
  a*Int[1/((e+f*x)*Sqrt[1+(c+d*x)^2]),x] + 
  b*Int[ArcSinh[c+d*x]/((e+f*x)*Sqrt[1+(c+d*x)^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && ZeroQ[d*e-c*f]


Int[(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_./((e_.+f_.*x_)^2*Sqrt[u_]),x_Symbol] :=
  -Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])^n/(f*(e+f*x)) + 
  b*n*d/f*Int[(a+b*ArcSinh[c+d*x])^(n-1)/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[n] && n>0


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  (e+f*x)^(m+1)*Sqrt[1+(c+d*x)^2]*(a+b*ArcSinh[c+d*x])^n/(f*(m+1)) - 
  b*n*d/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcSinh[c+d*x])^(n-1),x] - 
  d^2*(m+2)/(f^2*(m+1))*Int[(e+f*x)^(m+2)*(a+b*ArcSinh[c+d*x])^n/Sqrt[1+(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.+d_.*x_])/Sqrt[u_],x_Symbol] :=
  (e+f*x)^m*(c+d*x)*(a+b*ArcSinh[c+d*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,-(c+d*x)^2]/(d*(m+1)) - 
  b*(e+f*x)^m*(c+d*x)^2*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},-(c+d*x)^2]/(d*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && ZeroQ[d*e-c*f] && Not[NegativeIntegerQ[m]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_/Sqrt[u_],x_Symbol] :=
  (e+f*x)^m*(a+b*ArcSinh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*ArcSinh[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && RationalQ[m,n] && m>0 && n<-1


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_/Sqrt[u_],x_Symbol] :=
  2/(b*d^(m+1))*Subst[Int[x^(2*n+1)*(d*e-c*f+f*Sinh[x^2/b-a/b])^m,x],x,Sqrt[a+b*ArcSinh[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1+(c+d*x)^2)] && IntegerQ[m] && IntegerQ[n-1/2]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  1/(b*d^(m+1))*Subst[Int[x^n*(d*e-c*f+f*Sinh[x/b-a/b])^m,x],x,a+b*ArcSinh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[u-(1+(c+d*x)^2)] && IntegerQ[m] && Not[IntegerQ[n-1/2]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcSinh[c+d*x])^n/Sqrt[1+(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[u-(1+(c+d*x)^2)]


Int[1/(Sqrt[u_]*Sqrt[v_]*(a_.+b_.*ArcCosh[c_.+d_.*x_])),x_Symbol] :=
  Log[a+b*ArcCosh[c+d*x]]/(b*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)]


Int[(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_./(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  (a+b*ArcCosh[c+d*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_./(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  f*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])^n/d^2 - 
  b*f*n/d*Int[(a+b*ArcCosh[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && ZeroQ[d*e-c*f] && RationalQ[n] && n>0


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_./(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  f*(e+f*x)^(m-1)*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])^n/(d^2*m) - 
  b*f*n/(d*m)*Int[(e+f*x)^(m-1)*(a+b*ArcCosh[c+d*x])^(n-1),x] + 
  f^2*(m-1)/(d^2*m)*Int[(e+f*x)^(m-2)*(a+b*ArcCosh[c+d*x])^n/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && ZeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m>1


Int[ArcCosh[c_.+d_.*x_]/((e_.+f_.*x_)*Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  -2*ArcCosh[c+d*x]*ArcTan[c+d*x-Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]]/f - 
  I*PolyLog[2,-I*(c+d*x-Sqrt[-1+c+d*x]*Sqrt[1+c+d*x])]/f + 
  I*PolyLog[2,I*(c+d*x-Sqrt[-1+c+d*x]*Sqrt[1+c+d*x])]/f /;
FreeQ[{c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && ZeroQ[d*e-c*f]


Int[(a_+b_.*ArcCosh[c_.+d_.*x_])/((e_.+f_.*x_)*Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  a*Int[1/((e+f*x)*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] + 
  b*Int[ArcCosh[c+d*x]/((e+f*x)*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && ZeroQ[d*e-c*f]


Int[(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_./((e_.+f_.*x_)^2*Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])^n/(f*(e+f*x)) - 
  b*n*d/f*Int[(a+b*ArcCosh[c+d*x])^(n-1)/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && ZeroQ[d*e-c*f] && RationalQ[n] && n>0


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_./(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  -(e+f*x)^(m+1)*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]*(a+b*ArcCosh[c+d*x])^n/(f*(m+1)) + 
  b*n*d/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcCosh[c+d*x])^(n-1),x] + 
  d^2*(m+2)/(f^2*(m+1))*Int[(e+f*x)^(m+2)*(a+b*ArcCosh[c+d*x])^n/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && ZeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.+d_.*x_])/(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  (e+f*x)^m*(c+d*x)*Sqrt[1-(c+d*x)^2]*(a+b*ArcCosh[c+d*x])*
    Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,(c+d*x)^2]/(d*(m+1)*Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]) + 
  b*(e+f*x)^m*(c+d*x)^2*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},(c+d*x)^2]/(d*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && ZeroQ[d*e-c*f] && Not[NegativeIntegerQ[m]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_/(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  (e+f*x)^m*(a+b*ArcCosh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*ArcCosh[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && RationalQ[m,n] && m>0 && n<-1


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_/(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  2/(b*d^(m+1))*Subst[Int[x^(2*n+1)*(d*e-c*f+f*Cosh[x^2/b-a/b])^m,x],x,Sqrt[a+b*ArcCosh[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && IntegerQ[m] && IntegerQ[n-1/2]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_./(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  1/(b*d^(m+1))*Subst[Int[x^n*(d*e-c*f+f*Cosh[x/b-a/b])^m,x],x,a+b*ArcCosh[c+d*x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)] && IntegerQ[m] && Not[IntegerQ[n-1/2]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_])^n_./(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcCosh[c+d*x])^n/(Sqrt[-1+c+d*x]*Sqrt[1+c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[u-(-1+c+d*x)] && ZeroQ[v-(1+c+d*x)]


Int[x_^q_.*(a_.+b_.*ArcSinh[c_.+d_.*x_^p_])^n_.,x_Symbol] :=
  1/p*Subst[Int[(a+b*ArcSinh[c+d*x])^n,x],x,x^p] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[q-(p-1)]


Int[x_^q_.*(a_.+b_.*ArcCosh[c_.+d_.*x_^p_])^n_.,x_Symbol] :=
  1/p*Subst[Int[(a+b*ArcCosh[c+d*x])^n,x],x,x^p] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[q-(p-1)]


Int[x_^q_.*(e_.+f_.*x_^p_)^m_.*(a_.+b_.*ArcSinh[c_.+d_.*x_^p_])^n_.,x_Symbol] :=
  1/p*Subst[Int[(e+f*x)^m*(a+b*ArcSinh[c+d*x])^n,x],x,x^p] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[q-(p-1)]


Int[x_^q_.*(e_.+f_.*x_^p_)^m_.*(a_.+b_.*ArcCosh[c_.+d_.*x_^p_])^n_.,x_Symbol] :=
  1/p*Subst[Int[(e+f*x)^m*(a+b*ArcCosh[c+d*x])^n,x],x,x^p] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[q-(p-1)]


Int[ArcSinh[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Coth[x],x],x,ArcSinh[a*x^p]] /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0


Int[ArcCosh[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Tanh[x],x],x,ArcCosh[a*x^p]] /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0


Int[u_.*ArcSinh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCsch[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCosh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSech[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_^m_.*ArcSinh[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[x^n*Cosh[x]^(2*m+1),x],x,ArcSinh[a+b*x]] /;
FreeQ[{a,b,n},x] && ZeroQ[u-(1+(a+b*x)^2)] && IntegerQ[2*m]


Int[u_^m_*v_^m_*ArcCosh[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[x^n*Sinh[x]^(2*m+1),x],x,ArcCosh[a+b*x]] /;
FreeQ[{a,b,n},x] && ZeroQ[u-(-1+a+b*x)] && ZeroQ[v-(1+a+b*x)] && IntegerQ[m+1/2]


Int[f_^(c_.*ArcSinh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[f^(c*x^n)*Cosh[x],x],x,ArcSinh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[f_^(c_.*ArcCosh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[f^(c*x^n)*Sinh[x],x],x,ArcCosh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[x_^m_.*f_^(c_.*ArcSinh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[(-a/b+Sinh[x]/b)^m*f^(c*x^n)*Cosh[x],x],x,ArcSinh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[m,n]


Int[x_^m_.*f_^(c_.*ArcCosh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[(-a/b+Cosh[x]/b)^m*f^(c*x^n)*Sinh[x],x],x,ArcCosh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[m,n]


Int[(c_.+d_.*x_^2)^n_*ArcSinh[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcSinh[a*x],u,x] - 
  a*Int[Dist[1/Sqrt[1+a^2*x^2],u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[n+1/2] && n<=-1


Int[(c_.+d_.*x_^2)^n_*ArcCosh[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcCosh[a*x],u,x] - 
  a*Sqrt[1-a^2*x^2]/(Sqrt[-1+a*x]*Sqrt[1+a*x])*Int[Dist[1/Sqrt[1-a^2*x^2],u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[n+1/2] && n<=-1


Int[x_^m_.*(c_.+d_.*x_^2)^n_*ArcSinh[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(c+d*x^2)^n,x]]},  
  Dist[ArcSinh[a*x],u,x] - 
  a*Int[Dist[1/Sqrt[1+a^2*x^2],u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[n+1/2] && ZeroQ[a^2*c-d] && (EvenQ[m] || PositiveIntegerQ[m]) 


Int[x_^m_.*(c_.+d_.*x_^2)^n_*ArcCosh[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(c+d*x^2)^n,x]]},  
  Dist[ArcCosh[a*x],u,x] - 
  a*Sqrt[1-a^2*x^2]/(Sqrt[-1+a*x]*Sqrt[1+a*x])*Int[Dist[1/Sqrt[1-a^2*x^2],u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[n+1/2] && ZeroQ[a^2*c+d] && (EvenQ[m] || PositiveIntegerQ[m]) 


Int[ArcSinh[u_],x_Symbol] :=
  x*ArcSinh[u] -
  Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1+u^2],x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCosh[u_],x_Symbol] :=
  x*ArcCosh[u] - 
  Int[SimplifyIntegrand[x*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[x_^m_.*ArcSinh[u_],x_Symbol] :=
  x^(m+1)*ArcSinh[u]/(m+1) -
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/Sqrt[1+u^2],x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	Not[FunctionOfExponentialQ[u,x]]


Int[x_^m_.*ArcCosh[u_],x_Symbol] :=
  x^(m+1)*ArcCosh[u]/(m+1) -
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	Not[FunctionOfExponentialQ[u,x]]


Int[E^(n_.*ArcSinh[u_]), x_Symbol] :=
  Int[(u+Sqrt[1+u^2])^n,x] /;
IntegerQ[n] && PolynomialQ[u,x]


Int[x_^m_.*E^(n_.*ArcSinh[u_]), x_Symbol] :=
  Int[x^m*(u+Sqrt[1+u^2])^n,x] /;
RationalQ[m] && IntegerQ[n] && PolynomialQ[u,x]


Int[E^(n_.*ArcCosh[u_]), x_Symbol] :=
  Int[(u+Sqrt[-1+u]*Sqrt[1+u])^n,x] /;
IntegerQ[n] && PolynomialQ[u,x]


Int[x_^m_.*E^(n_.*ArcCosh[u_]), x_Symbol] :=
  Int[x^m*(u+Sqrt[-1+u]*Sqrt[1+u])^n,x] /;
RationalQ[m] && IntegerQ[n] && PolynomialQ[u,x]


Int[ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  x*ArcTanh[a*x]^n - a*n*Int[x*ArcTanh[a*x]^(n-1)/(1-a^2*x^2),x] /;
FreeQ[a,x] && PositiveIntegerQ[n]


Int[ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  x*ArcCoth[a*x]^n - a*n*Int[x*ArcCoth[a*x]^(n-1)/(1-a^2*x^2),x] /;
FreeQ[a,x] && PositiveIntegerQ[n]


Int[ArcTanh[a_.*x_]^n_,x_Symbol] :=
  Defer[Int][ArcTanh[a*x]^n,x] /;
FreeQ[{a,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcCoth[a_.*x_]^n_,x_Symbol] :=
  Defer[Int][ArcCoth[a*x]^n,x] /;
FreeQ[{a,n},x] && Not[PositiveIntegerQ[n]]


Int[x_*ArcTanh[a_.*x_],x_Symbol] :=
  x/(2*a) + x^2*ArcTanh[a*x]/2 - ArcTanh[a*x]/(2*a^2) /;
FreeQ[a,x]


Int[x_*ArcCoth[a_.*x_],x_Symbol] :=
  x/(2*a) + x^2*ArcCoth[a*x]/2 - ArcCoth[a*x]/(2*a^2) /;
FreeQ[a,x]


Int[x_^m_*ArcTanh[a_.*x_],x_Symbol] :=
  x^m/(a*m*(m+1)) + 
  x^(m+1)*ArcTanh[a*x]/(m+1) - 
  x^(m-1)*ArcTanh[a*x]/(a^2*(m+1)) + 
  (m-1)/(a^2*(m+1))*Int[x^(m-2)*ArcTanh[a*x],x] /;
FreeQ[a,x] && RationalQ[m] && m>1


Int[x_^m_*ArcCoth[a_.*x_],x_Symbol] :=
  x^m/(a*m*(m+1)) + 
  x^(m+1)*ArcCoth[a*x]/(m+1) - 
  x^(m-1)*ArcCoth[a*x]/(a^2*(m+1)) + 
  (m-1)/(a^2*(m+1))*Int[x^(m-2)*ArcCoth[a*x],x] /;
FreeQ[a,x] && RationalQ[m] && m>1


Int[ArcTanh[a_.*x_]/x_,x_Symbol] :=
  1/2*Int[Log[1+a*x]/x,x] -
  1/2*Int[Log[1-a*x]/x,x] /;
FreeQ[a,x]


Int[ArcCoth[a_.*x_]/x_,x_Symbol] :=
  1/2*Int[Log[1+1/(a*x)]/x,x] -
  1/2*Int[Log[1-1/(a*x)]/x,x] /;
FreeQ[a,x]


Int[ArcTanh[a_.*x_]/x_^2,x_Symbol] :=
  -ArcTanh[a*x]/x - a*ArcTanh[1-2*a^2*x^2] /;
FreeQ[a,x]


Int[ArcCoth[a_.*x_]/x_^2,x_Symbol] :=
  -ArcCoth[a*x]/x - a*ArcCoth[1-2*a^2*x^2] /;
FreeQ[a,x]


Int[ArcTanh[a_.*x_]/x_^3,x_Symbol] :=
  -a/(2*x) - ArcTanh[a*x]/(2*x^2) + a^2*ArcTanh[a*x]/2 /;
FreeQ[a,x]


Int[ArcCoth[a_.*x_]/x_^3,x_Symbol] :=
  -a/(2*x) - ArcCoth[a*x]/(2*x^2) + a^2*ArcCoth[a*x]/2 /;
FreeQ[a,x]


Int[x_^m_*ArcTanh[a_.*x_],x_Symbol] :=
  -a*x^(m+2)/((m+1)*(m+2)) + 
  x^(m+1)*ArcTanh[a*x]/(m+1) - 
  a^2*x^(m+3)*ArcTanh[a*x]/(m+1) + 
  a^2*(m+3)/(m+1)*Int[x^(m+2)*ArcTanh[a*x],x] /;
FreeQ[a,x] && RationalQ[m] && m<-3


Int[x_^m_*ArcCoth[a_.*x_],x_Symbol] :=
  -a*x^(m+2)/((m+1)*(m+2)) + 
  x^(m+1)*ArcCoth[a*x]/(m+1) - 
  a^2*x^(m+3)*ArcCoth[a*x]/(m+1) + 
  a^2*(m+3)/(m+1)*Int[x^(m+2)*ArcCoth[a*x],x] /;
FreeQ[a,x] && RationalQ[m] && m<-3


Int[ArcTanh[a_.*x_]^n_./x_,x_Symbol] :=
  2*ArcTanh[a*x]^n*ArcTanh[1-2/(1-a*x)] -
  2*a*n*Int[ArcTanh[a*x]^(n-1)*ArcTanh[1-2/(1-a*x)]/(1-a^2*x^2),x] /;
FreeQ[a,x] && IntegerQ[n] && n>1


Int[ArcCoth[a_.*x_]^n_./x_,x_Symbol] :=
  2*ArcCoth[a*x]^n*ArcCoth[1-2/(1-a*x)] -
  2*a*n*Int[ArcCoth[a*x]^(n-1)*ArcCoth[1-2/(1-a*x)]/(1-a^2*x^2),x] /;
FreeQ[a,x] && IntegerQ[n] && n>1


Int[x_^m_.*ArcTanh[a_.*x_]^n_,x_Symbol] :=
  x^(m+1)*ArcTanh[a*x]^n/(m+1) - 
  a*n/(m+1)*Int[x^(m+1)*ArcTanh[a*x]^(n-1)/(1-a^2*x^2),x] /;
FreeQ[{a,m},x] && IntegerQ[n] && n>1 && NonzeroQ[m+1]


Int[x_^m_.*ArcCoth[a_.*x_]^n_,x_Symbol] :=
  x^(m+1)*ArcCoth[a*x]^n/(m+1) - 
  a*n/(m+1)*Int[x^(m+1)*ArcCoth[a*x]^(n-1)/(1-a^2*x^2),x] /;
FreeQ[{a,m},x] && IntegerQ[n] && n>1 && NonzeroQ[m+1]


Int[x_^m_.*ArcTanh[a_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcTanh[a*x]^n,x] /;
FreeQ[{a,m,n},x] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*ArcCoth[a_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcCoth[a*x]^n,x] /;
FreeQ[{a,m,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcTanh[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  -ArcTanh[a*x]^n*Log[2*c/(c+d*x)]/d +
  a*n/d*Int[ArcTanh[a*x]^(n-1)*Log[2*c/(c+d*x)]/(1-a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n]


Int[ArcCoth[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  -ArcCoth[a*x]^n*Log[2*c/(c+d*x)]/d +
  a*n/d*Int[ArcCoth[a*x]^(n-1)*Log[2*c/(c+d*x)]/(1-a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n]


Int[ArcTanh[a_.*x_]^n_/(c_+d_.*x_),x_Symbol] :=
  Defer[Int][ArcTanh[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c^2-d^2] && Not[PositiveIntegerQ[n]]


Int[ArcCoth[a_.*x_]^n_/(c_+d_.*x_),x_Symbol] :=
  Defer[Int][ArcCoth[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c^2-d^2] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*ArcTanh[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  1/d*Int[x^(m-1)*ArcTanh[a*x]^n,x] -
  c/d*Int[x^(m-1)*ArcTanh[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  1/d*Int[x^(m-1)*ArcCoth[a*x]^n,x] -
  c/d*Int[x^(m-1)*ArcCoth[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[ArcTanh[a_.*x_]^n_./(x_*(c_+d_.*x_)),x_Symbol] :=
  ArcTanh[a*x]^n*Log[2*d*x/(c+d*x)]/c - 
  a*n/c*Int[ArcTanh[a*x]^(n-1)*Log[2*d*x/(c+d*x)]/(1-a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n]


Int[ArcTanh[a_.*x_]^n_./(c_.*x_+d_.*x_^2),x_Symbol] :=
  ArcTanh[a*x]^n*Log[2*d*x/(c+d*x)]/c - 
  a*n/c*Int[ArcTanh[a*x]^(n-1)*Log[2*d*x/(c+d*x)]/(1-a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n]


Int[ArcCoth[a_.*x_]^n_./(x_*(c_+d_.*x_)),x_Symbol] :=
  ArcCoth[a*x]^n*Log[2*d*x/(c+d*x)]/c - 
  a*n/c*Int[ArcCoth[a*x]^(n-1)*Log[2*d*x/(c+d*x)]/(1-a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n]


Int[ArcCoth[a_.*x_]^n_./(c_.*x_+d_.*x_^2),x_Symbol] :=
  ArcCoth[a*x]^n*Log[2*d*x/(c+d*x)]/c - 
  a*n/c*Int[ArcCoth[a*x]^(n-1)*Log[2*d*x/(c+d*x)]/(1-a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n]


Int[x_^m_*ArcTanh[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  1/c*Int[x^m*ArcTanh[a*x]^n,x] -
  d/c*Int[x^(m+1)*ArcTanh[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_*ArcCoth[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  1/c*Int[x^m*ArcCoth[a*x]^n,x] -
  d/c*Int[x^(m+1)*ArcCoth[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_.*ArcTanh[a_.*x_]^n_/(c_+d_.*x_),x_Symbol] :=
  Defer[Int][x^m*ArcTanh[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d,m,n},x] && ZeroQ[a^2*c^2-d^2] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*ArcCoth[a_.*x_]^n_/(c_+d_.*x_),x_Symbol] :=
  Defer[Int][x^m*ArcCoth[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d,m,n},x] && ZeroQ[a^2*c^2-d^2] && Not[PositiveIntegerQ[n]]


Int[(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_],x_Symbol] :=
  (c+d*x^2)^p/(2*a*p*(2*p+1)) +
  x*(c+d*x^2)^p*ArcTanh[a*x]/(2*p+1) +
  2*c*p/(2*p+1)*Int[(c+d*x^2)^(p-1)*ArcTanh[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p>0


Int[(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_],x_Symbol] :=
  (c+d*x^2)^p/(2*a*p*(2*p+1)) +
  x*(c+d*x^2)^p*ArcCoth[a*x]/(2*p+1) +
  2*c*p/(2*p+1)*Int[(c+d*x^2)^(p-1)*ArcCoth[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p>0


Int[(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_,x_Symbol] :=
  n*(c+d*x^2)^p*ArcTanh[a*x]^(n-1)/(2*a*p*(2*p+1)) + 
  x*(c+d*x^2)^p*ArcTanh[a*x]^n/(2*p+1) + 
  2*c*p/(2*p+1)*Int[(c+d*x^2)^(p-1)*ArcTanh[a*x]^n,x] - 
  c*n*(n-1)/(2*p*(2*p+1))*Int[(c+d*x^2)^(p-1)*ArcTanh[a*x]^(n-2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n,p] && p>0 && n>1


Int[(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_,x_Symbol] :=
  n*(c+d*x^2)^p*ArcCoth[a*x]^(n-1)/(2*a*p*(2*p+1)) + 
  x*(c+d*x^2)^p*ArcCoth[a*x]^n/(2*p+1) + 
  2*c*p/(2*p+1)*Int[(c+d*x^2)^(p-1)*ArcCoth[a*x]^n,x] - 
  c*n*(n-1)/(2*p*(2*p+1))*Int[(c+d*x^2)^(p-1)*ArcCoth[a*x]^(n-2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n,p] && p>0 && n>1


Int[1/((c_+d_.*x_^2)*ArcTanh[a_.*x_]),x_Symbol] :=
  Log[ArcTanh[a*x]]/(a*c) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]


Int[1/((c_+d_.*x_^2)*ArcCoth[a_.*x_]),x_Symbol] :=
  Log[ArcCoth[a*x]]/(a*c) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]


Int[ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  ArcTanh[a*x]^(n+1)/(a*c*(n+1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n+1]


Int[ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  ArcCoth[a*x]^(n+1)/(a*c*(n+1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n+1]


Int[ArcTanh[a_.*x_]/Sqrt[u_],x_Symbol] :=
  -2*ArcTanh[a*x]*ArcTan[Sqrt[1-a*x]/Sqrt[1+a*x]]/a - 
  I*PolyLog[2,-I*Sqrt[1-a*x]/Sqrt[1+a*x]]/a + 
  I*PolyLog[2,I*Sqrt[1-a*x]/Sqrt[1+a*x]]/a /;
FreeQ[a,x] && ZeroQ[u-(1-a^2*x^2)]


Int[ArcCoth[a_.*x_]/Sqrt[u_],x_Symbol] :=
  -2*ArcCoth[a*x]*ArcTan[Sqrt[1-a*x]/Sqrt[1+a*x]]/a - 
  I*PolyLog[2,-I*Sqrt[1-a*x]/Sqrt[1+a*x]]/a + 
  I*PolyLog[2,I*Sqrt[1-a*x]/Sqrt[1+a*x]]/a /;
FreeQ[a,x] && ZeroQ[u-(1-a^2*x^2)]


Int[ArcTanh[a_.*x_]^n_./Sqrt[u_],x_Symbol] :=
  1/a*Subst[Int[x^n*Sech[x],x],x,ArcTanh[a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1-a^2*x^2)] && IntegerQ[n] && n>1


Int[ArcCoth[a_.*x_]^n_./Sqrt[u_],x_Symbol] :=
  -x*Sqrt[1-1/(a^2*x^2)]/Sqrt[1-a^2*x^2]*Subst[Int[x^n*Csch[x],x],x,ArcCoth[a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1-a^2*x^2)] && IntegerQ[n] && n>1


Int[ArcTanh[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcTanh[a*x]^n/Sqrt[1-a^2*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n] && NonzeroQ[c-1]


Int[ArcCoth[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcCoth[a*x]^n/Sqrt[1-a^2*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n] && NonzeroQ[c-1]


Int[ArcTanh[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Defer[Int][ArcTanh[a*x]^n/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[PositiveIntegerQ[n]]


Int[ArcCoth[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Defer[Int][ArcCoth[a*x]^n/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[PositiveIntegerQ[n]]


Int[ArcTanh[a_.*x_]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -1/(a*c*Sqrt[c+d*x^2]) +
  x*ArcTanh[a*x]/(c*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]


Int[ArcCoth[a_.*x_]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -1/(a*c*Sqrt[c+d*x^2]) +
  x*ArcCoth[a*x]/(c*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]


Int[ArcTanh[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -n*ArcTanh[a*x]^(n-1)/(a*c*Sqrt[c+d*x^2]) +
  x*ArcTanh[a*x]^n/(c*Sqrt[c+d*x^2]) +
  n*(n-1)*Int[ArcTanh[a*x]^(n-2)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>1


Int[ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -n*ArcCoth[a*x]^(n-1)/(a*c*Sqrt[c+d*x^2]) +
  x*ArcCoth[a*x]^n/(c*Sqrt[c+d*x^2]) +
  n*(n-1)*Int[ArcCoth[a*x]^(n-2)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>1


Int[1/((c_+d_.*x_^2)^(3/2)*ArcTanh[a_.*x_]),x_Symbol] :=
  1/(a*c^(3/2))*Subst[Int[Cosh[x]/x,x],x,ArcTanh[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveQ[c]


Int[1/((c_+d_.*x_^2)^(3/2)*ArcTanh[a_.*x_]),x_Symbol] :=
  Sqrt[c+d*x^2]/(c^2*Sqrt[1-a^2*x^2])*Int[1/((1-a^2*x^2)^(3/2)*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]]


Int[1/((c_+d_.*x_^2)^(3/2)*ArcCoth[a_.*x_]),x_Symbol] :=
  x*Sqrt[(a^2*x^2-1)/(a^2*x^2)]/(c*Sqrt[c+d*x^2])*Subst[Int[Sinh[x]/x,x],x,ArcCoth[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]


Int[1/((c_+d_.*x_^2)^(3/2)*ArcTanh[a_.*x_]^2),x_Symbol] :=
  -1/(a*c*Sqrt[c+d*x^2]*ArcTanh[a*x]) + 
  a*Int[x/((c+d*x^2)^(3/2)*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]


Int[1/((c_+d_.*x_^2)^(3/2)*ArcCoth[a_.*x_]^2),x_Symbol] :=
  -1/(a*c*Sqrt[c+d*x^2]*ArcCoth[a*x]) + 
  a*Int[x/((c+d*x^2)^(3/2)*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]


Int[ArcTanh[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  ArcTanh[a*x]^(n+1)/(a*c*(n+1)*Sqrt[c+d*x^2]) -
  x*ArcTanh[a*x]^(n+2)/(c*(n+1)*(n+2)*Sqrt[c+d*x^2]) +
  1/((n+1)*(n+2))*Int[ArcTanh[a*x]^(n+2)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1 && n!=-2


Int[ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  ArcCoth[a*x]^(n+1)/(a*c*(n+1)*Sqrt[c+d*x^2]) -
  x*ArcCoth[a*x]^(n+2)/(c*(n+1)*(n+2)*Sqrt[c+d*x^2]) +
  1/((n+1)*(n+2))*Int[ArcCoth[a*x]^(n+2)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1 && n!=-2


Int[(c_+d_.*x_^2)^p_*ArcTanh[a_.*x_],x_Symbol] :=
  -(c+d*x^2)^(p+1)/(4*a*c*(p+1)^2) -
  x*(c+d*x^2)^(p+1)*ArcTanh[a*x]/(2*c*(p+1)) +
  (2*p+3)/(2*c*(p+1))*Int[(c+d*x^2)^(p+1)*ArcTanh[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p<-1 && p!=-3/2


Int[(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_],x_Symbol] :=
  -(c+d*x^2)^(p+1)/(4*a*c*(p+1)^2) -
  x*(c+d*x^2)^(p+1)*ArcCoth[a*x]/(2*c*(p+1)) +
  (2*p+3)/(2*c*(p+1))*Int[(c+d*x^2)^(p+1)*ArcCoth[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p<-1 && p!=-3/2


Int[(c_+d_.*x_^2)^p_*Sqrt[ArcTanh[a_.*x_]],x_Symbol] :=
  2*c^p/a*Subst[Int[x^2*Sech[x^2]^(2*(p+1)),x],x,Sqrt[ArcTanh[a*x]]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[p] && p<-1


Int[(c_+d_.*x_^2)^p_*Sqrt[ArcCoth[a_.*x_]],x_Symbol] :=
  -2*(-c)^p/a*Subst[Int[x^2*Csch[x^2]^(2*(p+1)),x],x,Sqrt[ArcCoth[a*x]]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[p] && p<-1


Int[(c_+d_.*x_^2)^p_*ArcTanh[a_.*x_]^n_,x_Symbol] :=
  -n*(c+d*x^2)^(p+1)*ArcTanh[a*x]^(n-1)/(4*a*c*(p+1)^2) -
  x*(c+d*x^2)^(p+1)*ArcTanh[a*x]^n/(2*c*(p+1)) +
  (2*p+3)/(2*c*(p+1))*Int[(c+d*x^2)^(p+1)*ArcTanh[a*x]^n,x] +
  n*(n-1)/(4*(p+1)^2)*Int[(c+d*x^2)^p*ArcTanh[a*x]^(n-2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p,n] && p<-1 && p!=-3/2 && n>1


Int[(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
  -n*(c+d*x^2)^(p+1)*ArcCoth[a*x]^(n-1)/(4*a*c*(p+1)^2) -
  x*(c+d*x^2)^(p+1)*ArcCoth[a*x]^n/(2*c*(p+1)) +
  (2*p+3)/(2*c*(p+1))*Int[(c+d*x^2)^(p+1)*ArcCoth[a*x]^n,x] +
  n*(n-1)/(4*(p+1)^2)*Int[(c+d*x^2)^p*ArcCoth[a*x]^(n-2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p,n] && p<-1 && p!=-3/2 && n>1


Int[(c_+d_.*x_^2)^p_/ArcTanh[a_.*x_],x_Symbol] :=
  c^p/a*Subst[Int[Expand[TrigReduce[Sech[x]^(2*(p+1))/x]],x],x,ArcTanh[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[2*p] && p<-1 && (IntegerQ[p] || PositiveQ[c])


Int[(c_+d_.*x_^2)^p_/ArcCoth[a_.*x_],x_Symbol] :=
  -(-c)^p/a*Subst[Int[Expand[TrigReduce[Csch[x]^(2*(p+1))/x]],x],x,ArcCoth[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[2*p] && p<-1 && (IntegerQ[p] || PositiveQ[c])


Int[(c_+d_.*x_^2)^p_/ArcTanh[a_.*x_],x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[(1-a^2*x^2)^p/ArcTanh[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[p+1/2] && p<-1 && Not[PositiveQ[c]]


Int[(c_+d_.*x_^2)^p_/ArcCoth[a_.*x_],x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[(1-a^2*x^2)^p/ArcCoth[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[p+1/2] && p<-1 && Not[PositiveQ[c]]


Int[(c_+d_.*x_^2)^p_*ArcTanh[a_.*x_]^n_,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcTanh[a*x]^(n+1)/(a*c*(n+1)) +
  2*a*(p+1)/(n+1)*Int[x*(c+d*x^2)^p*ArcTanh[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p,n] && p<-1 && p!=-3/2 && n<-1


Int[(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcCoth[a*x]^(n+1)/(a*c*(n+1)) +
  2*a*(p+1)/(n+1)*Int[x*(c+d*x^2)^p*ArcCoth[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p,n] && p<-1 && p!=-3/2 && n<-1


Int[(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  Defer[Int][(c+d*x^2)^p*ArcTanh[a*x]^n,x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d]


Int[(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  Defer[Int][(c+d*x^2)^p*ArcCoth[a*x]^n,x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d]


Int[x_*(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcTanh[a*x]^n/(2*d*(p+1)) +
  n/(2*a*(p+1))*Int[(c+d*x^2)^p*ArcTanh[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p>0 && PositiveIntegerQ[n]


Int[x_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcCoth[a*x]^n/(2*d*(p+1)) +
  n/(2*a*(p+1))*Int[(c+d*x^2)^p*ArcCoth[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p>0 && PositiveIntegerQ[n]


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  x^(m+1)*(c+d*x^2)^(p+1)*ArcTanh[a*x]^n/(c*(m+1)) -
  a*n/(m+1)*Int[x^(m+1)*(c+d*x^2)^p*ArcTanh[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,p] && p>0 && PositiveIntegerQ[n] && ZeroQ[m+2*p+3]


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  x^(m+1)*(c+d*x^2)^(p+1)*ArcCoth[a*x]^n/(c*(m+1)) -
  a*n/(m+1)*Int[x^(m+1)*(c+d*x^2)^p*ArcCoth[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,p] && p>0 && PositiveIntegerQ[n] && ZeroQ[m+2*p+3]


Int[x_^m_.*Sqrt[c_+d_.*x_^2]*ArcTanh[a_.*x_],x_Symbol] :=
  x^(m+1)*Sqrt[c+d*x^2]*ArcTanh[a*x]/(m+2) - 
  a*c/(m+2)*Int[x^(m+1)/Sqrt[c+d*x^2],x] + 
  c/(m+2)*Int[x^m*ArcTanh[a*x]/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && NonzeroQ[m+2]


Int[x_^m_.*Sqrt[c_+d_.*x_^2]*ArcCoth[a_.*x_],x_Symbol] :=
  x^(m+1)*Sqrt[c+d*x^2]*ArcCoth[a*x]/(m+2) - 
  a*c/(m+2)*Int[x^(m+1)/Sqrt[c+d*x^2],x] + 
  c/(m+2)*Int[x^m*ArcCoth[a*x]/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && NonzeroQ[m+2]


Int[x_^m_.*(c_+d_.*x_^2)^p_*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(c+d*x^2)^p*ArcTanh[a*x]^n,x],x] /;
FreeQ[{a,c,d,m},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_.*(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(c+d*x^2)^p*ArcCoth[a*x]^n,x],x] /;
FreeQ[{a,c,d,m},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  c*Int[x^m*(c+d*x^2)^(p-1)*ArcTanh[a*x]^n,x] - 
  a^2*c*Int[x^(m+2)*(c+d*x^2)^(p-1)*ArcTanh[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,p] && p>0 && PositiveIntegerQ[n] && NonzeroQ[m+2*p+3]


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  c*Int[x^m*(c+d*x^2)^(p-1)*ArcCoth[a*x]^n,x] - 
  a^2*c*Int[x^(m+2)*(c+d*x^2)^(p-1)*ArcCoth[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,p] && p>0 && PositiveIntegerQ[n] && NonzeroQ[m+2*p+3]


Int[x_*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  ArcTanh[a*x]^(n+1)/(d*(n+1)) +
  1/(a*c)*Int[ArcTanh[a*x]^n/(1-a*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[x_*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  ArcCoth[a*x]^(n+1)/(d*(n+1)) +
  1/(a*c)*Int[ArcCoth[a*x]^n/(1-a*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[x_^m_*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/d*Int[x^(m-2)*ArcTanh[a*x]^n,x] -
  c/d*Int[x^(m-2)*ArcTanh[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/d*Int[x^(m-2)*ArcCoth[a*x]^n,x] -
  c/d*Int[x^(m-2)*ArcCoth[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n] && n>0 && m>1


Int[ArcTanh[a_.*x_]^n_./(x_*(c_+d_.*x_^2)),x_Symbol] :=
  ArcTanh[a*x]^(n+1)/(c*(n+1)) +
  1/c*Int[ArcTanh[a*x]^n/(x*(1+a*x)),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[ArcTanh[a_.*x_]^n_./(c_.*x_+d_.*x_^3),x_Symbol] :=
  ArcTanh[a*x]^(n+1)/(c*(n+1)) +
  1/c*Int[ArcTanh[a*x]^n/(x*(1+a*x)),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[ArcCoth[a_.*x_]^n_./(x_*(c_+d_.*x_^2)),x_Symbol] :=
  ArcCoth[a*x]^(n+1)/(c*(n+1)) +
  1/c*Int[ArcCoth[a*x]^n/(x*(1+a*x)),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[ArcCoth[a_.*x_]^n_./(c_.*x_+d_.*x_^3),x_Symbol] :=
  ArcCoth[a*x]^(n+1)/(c*(n+1)) +
  1/c*Int[ArcCoth[a*x]^n/(x*(1+a*x)),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[x_^m_*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/c*Int[x^m*ArcTanh[a*x]^n,x] -
  d/c*Int[x^(m+2)*ArcTanh[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/c*Int[x^m*ArcCoth[a*x]^n,x] -
  d/c*Int[x^(m+2)*ArcCoth[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_.*ArcTanh[a_.*x_]^n_/(c_+d_.*x_^2),x_Symbol] :=
  x^m*ArcTanh[a*x]^(n+1)/(a*c*(n+1)) - 
  m/(a*c*(n+1))*Int[x^(m-1)*ArcTanh[a*x]^(n+1),x] /;
FreeQ[{a,c,d,m},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1


Int[x_^m_.*ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2),x_Symbol] :=
  x^m*ArcCoth[a*x]^(n+1)/(a*c*(n+1)) - 
  m/(a*c*(n+1))*Int[x^(m-1)*ArcCoth[a*x]^(n+1),x] /;
FreeQ[{a,c,d,m},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1


Int[x_*ArcTanh[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[c+d*x^2]*ArcTanh[a*x]^n/d + 
  n/a*Int[ArcTanh[a*x]^(n-1)/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[x_*ArcCoth[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[c+d*x^2]*ArcCoth[a*x]^n/d + 
  n/a*Int[ArcCoth[a*x]^(n-1)/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[x_^m_.*ArcTanh[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null},Int[x^m/Sqrt[c+d*x^2],x]]},
  Dist[ArcTanh[a*x]^n,u,x] - 
  a*c*n*Int[Dist[ArcTanh[a*x]^(n-1)/(c+d*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n,(m+1)/2]


Int[x_^m_.*ArcCoth[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null},Int[x^m/Sqrt[c+d*x^2],x]]},
  Dist[ArcCoth[a*x]^n,u,x] - 
  a*c*n*Int[Dist[ArcCoth[a*x]^(n-1)/(c+d*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n,(m+1)/2]


Int[x_^m_.*ArcTanh[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null},Int[(Binomial[m-1,m/2]-2^(m-1)*a^m*x^m)/Sqrt[c+d*x^2],x]]},
  Binomial[m-1,m/2]/(2^(m-1)*a^m)*Int[ArcTanh[a*x]^n/Sqrt[c+d*x^2],x] -
  Dist[ArcTanh[a*x]^n/(2^(m-1)*a^m),u,x] + 
  a*c*n/(2^(m-1)*a^m)*Int[Dist[ArcTanh[a*x]^(n-1)/(c+d*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n,m/2]


Int[x_^m_.*ArcCoth[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null},Int[(Binomial[m-1,m/2]-2^(m-1)*a^m*x^m)/Sqrt[c+d*x^2],x]]},
  Binomial[m-1,m/2]/(2^(m-1)*a^m)*Int[ArcCoth[a*x]^n/Sqrt[c+d*x^2],x] -
  Dist[ArcCoth[a*x]^n/(2^(m-1)*a^m),u,x] + 
  a*c*n/(2^(m-1)*a^m)*Int[Dist[ArcCoth[a*x]^(n-1)/(c+d*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n,m/2]


Int[ArcTanh[a_.*x_]/(x_*Sqrt[u_]),x_Symbol] :=
  -2*ArcTanh[a*x]*ArcTanh[Sqrt[1+a*x]/Sqrt[1-a*x]] + 
  2*PolyLog[2,Sqrt[1+a*x]/Sqrt[1-a*x]] - 
  1/2*PolyLog[2,(1+a*x)/(1-a*x)] /;
FreeQ[a,x] && ZeroQ[u-(1-a^2*x^2)]


Int[ArcCoth[a_.*x_]/(x_*Sqrt[u_]),x_Symbol] :=
  -2*ArcCoth[a*x]*ArcTanh[Sqrt[1+a*x]/Sqrt[1-a*x]] + 
  2*PolyLog[2,Sqrt[1+a*x]/Sqrt[1-a*x]] - 
  1/2*PolyLog[2,(1+a*x)/(1-a*x)] /;
FreeQ[a,x] && ZeroQ[u-(1-a^2*x^2)]


Int[ArcTanh[a_.*x_]^n_/(x_*Sqrt[u_]),x_Symbol] :=
  Subst[Int[x^n*Csch[x],x],x,ArcTanh[a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1-a^2*x^2)] && IntegerQ[n] && n>1


Int[ArcCoth[a_.*x_]^n_/(x_*Sqrt[u_]),x_Symbol] :=
  -a*x*Sqrt[1-1/(a^2*x^2)]/Sqrt[1-a^2*x^2]*Subst[Int[x^n*Sech[x],x],x,ArcCoth[a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1-a^2*x^2)] && IntegerQ[n] && n>1


Int[ArcTanh[a_.*x_]^n_./(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcTanh[a*x]^n/(x*Sqrt[1-a^2*x^2]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n] && NonzeroQ[c-1]


Int[ArcCoth[a_.*x_]^n_./(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcCoth[a*x]^n/(x*Sqrt[1-a^2*x^2]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveIntegerQ[n] && NonzeroQ[c-1]


Int[ArcTanh[a_.*x_]^n_./(x_^2*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  -Sqrt[c+d*x^2]*ArcTanh[a*x]^n/(c*x) + 
  a*n*Int[ArcTanh[a*x]^(n-1)/(x*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[ArcCoth[a_.*x_]^n_./(x_^2*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  -Sqrt[c+d*x^2]*ArcCoth[a*x]^n/(c*x) + 
  a*n*Int[ArcCoth[a*x]^(n-1)/(x*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0


Int[x_^m_*ArcTanh[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[c+d*x^2]*ArcTanh[a*x]^n/(c*(m+1)) - 
  a*n/(m+1)*Int[x^(m+1)*ArcTanh[a*x]^(n-1)/Sqrt[c+d*x^2],x] + 
  a^2*(m+2)/(m+1)*Int[x^(m+2)*ArcTanh[a*x]^n/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_^m_*ArcCoth[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[c+d*x^2]*ArcCoth[a*x]^n/(c*(m+1)) - 
  a*n/(m+1)*Int[x^(m+1)*ArcCoth[a*x]^(n-1)/Sqrt[c+d*x^2],x] + 
  a^2*(m+2)/(m+1)*Int[x^(m+2)*ArcCoth[a*x]^n/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_*(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcTanh[a*x]^n/(2*d*(p+1)) +
  n/(2*a*(p+1))*Int[(c+d*x^2)^p*ArcTanh[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n,p] && p<-1 && n>0


Int[x_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcCoth[a*x]^n/(2*d*(p+1)) +
  n/(2*a*(p+1))*Int[(c+d*x^2)^p*ArcCoth[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n,p] && p<-1 && n>0


Int[x_*ArcTanh[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  x*ArcTanh[a*x]^(n+1)/(a*c*(n+1)*Sqrt[c+d*x^2]) - 
  1/(a*(n+1))*Int[ArcTanh[a*x]^(n+1)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1


Int[x_*ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  x*ArcCoth[a*x]^(n+1)/(a*c*(n+1)*Sqrt[c+d*x^2]) - 
  1/(a*(n+1))*Int[ArcCoth[a*x]^(n+1)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1


Int[x_*(c_+d_.*x_^2)^p_./ArcTanh[a_.*x_]^2,x_Symbol] :=
  -x*(c+d*x^2)^(p+1)/(a*c*ArcTanh[a*x]) + 
  c^p/a^2*Subst[Int[Expand[TrigReduce[(p+2-(p+1)*Cosh[2*x])/(x*Cosh[x]^(2*(p+2)))]],x],x,ArcTanh[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[2*p] && p<-1 && (IntegerQ[p] || PositiveQ[c])


Int[x_*(c_+d_.*x_^2)^p_./ArcCoth[a_.*x_]^2,x_Symbol] :=
  -x*(c+d*x^2)^(p+1)/(a*c*ArcCoth[a*x]) - 
  (-c)^p/a^2*Subst[Int[Expand[TrigReduce[(p+2+(p+1)*Cosh[2*x])/(x*Sinh[x]^(2*(p+2)))]],x],x,ArcCoth[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[2*p] && p<-1 && (IntegerQ[p] || PositiveQ[c])


Int[x_*(c_+d_.*x_^2)^p_/ArcTanh[a_.*x_]^2,x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[x*(1-a^2*x^2)^p/ArcTanh[a*x]^2,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[p+1/2] && p<-1 && Not[PositiveQ[c]]


Int[x_*(c_+d_.*x_^2)^p_/ArcCoth[a_.*x_]^2,x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[x*(1-a^2*x^2)^p/ArcCoth[a*x]^2,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[p+1/2] && p<-1 && Not[PositiveQ[c]]


Int[x_*ArcTanh[a_.*x_]^n_/(c_+d_.*x_^2)^2,x_Symbol] :=
  x*ArcTanh[a*x]^(n+1)/(a*c*(n+1)*(c+d*x^2)) +
  (1+a^2*x^2)*ArcTanh[a*x]^(n+2)/(d*(n+1)*(n+2)*(c+d*x^2)) +
  4/((n+1)*(n+2))*Int[x*ArcTanh[a*x]^(n+2)/(c+d*x^2)^2,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1 && n!=-2


Int[x_*ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2)^2,x_Symbol] :=
  x*ArcCoth[a*x]^(n+1)/(a*c*(n+1)*(c+d*x^2)) +
  (1+a^2*x^2)*ArcCoth[a*x]^(n+2)/(d*(n+1)*(n+2)*(c+d*x^2)) +
  4/((n+1)*(n+2))*Int[x*ArcCoth[a*x]^(n+2)/(c+d*x^2)^2,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1 && n!=-2


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  x^m*(c+d*x^2)^(p+1)*ArcTanh[a*x]^(n+1)/(a*c*(n+1)) -
  m/(a*(n+1))*Int[x^(m-1)*(c+d*x^2)^p*ArcTanh[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n,p] && p<-1 && n<-1 && ZeroQ[m+2*p+2]


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  x^m*(c+d*x^2)^(p+1)*ArcCoth[a*x]^(n+1)/(a*c*(n+1)) -
  m/(a*(n+1))*Int[x^(m-1)*(c+d*x^2)^p*ArcCoth[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n,p] && p<-1 && n<-1 && ZeroQ[m+2*p+2]


Int[x_^m_.*(c_+d_.*x_^2)^p_/ArcTanh[a_.*x_],x_Symbol] :=
  c^p/a^(m+1)*Subst[Int[Expand[TrigReduce[Sinh[x]^m/(x*Cosh[x]^(m+2*(p+1)))]],x],x,ArcTanh[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,2*p] && (IntegerQ[p] || PositiveQ[c]) && 0<m<-(2*p+1)


Int[x_^m_.*(c_+d_.*x_^2)^p_/ArcCoth[a_.*x_],x_Symbol] :=
  -(-c)^p/a^(m+1)*Subst[Int[Expand[TrigReduce[Cosh[x]^m/(x*Sinh[x]^(m+2*(p+1)))]],x],x,ArcCoth[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,2*p] && (IntegerQ[p] || PositiveQ[c]) && 0<m<-(2*p+1)


Int[x_^m_.*(c_+d_.*x_^2)^p_/ArcTanh[a_.*x_],x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[x^m*(1-a^2*x^2)^p/ArcTanh[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,p+1/2] && Not[PositiveQ[c]] && 0<m<-(2*p+1)


Int[x_^m_.*(c_+d_.*x_^2)^p_/ArcCoth[a_.*x_],x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[x^m*(1-a^2*x^2)^p/ArcCoth[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,p+1/2] && Not[PositiveQ[c]] && 0<m<-(2*p+1)


Int[x_^m_*(c_+d_.*x_^2)^p_*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  1/d*Int[x^(m-2)*(c+d*x^2)^(p+1)*ArcTanh[a*x]^n,x] -
  c/d*Int[x^(m-2)*(c+d*x^2)^p*ArcTanh[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  1/d*Int[x^(m-2)*(c+d*x^2)^(p+1)*ArcCoth[a*x]^n,x] -
  c/d*Int[x^(m-2)*(c+d*x^2)^p*ArcCoth[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(c_+d_.*x_^2)^p_*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  1/c*Int[x^m*(c+d*x^2)^(p+1)*ArcTanh[a*x]^n,x] -
  d/c*Int[x^(m+2)*(c+d*x^2)^p*ArcTanh[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_*(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  1/c*Int[x^m*(c+d*x^2)^(p+1)*ArcCoth[a*x]^n,x] -
  d/c*Int[x^(m+2)*(c+d*x^2)^p*ArcCoth[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  x^m*(c+d*x^2)^(p+1)*ArcTanh[a*x]^(n+1)/(a*c*(n+1)) - 
  m/(a*(n+1))*Int[x^(m-1)*(c+d*x^2)^p*ArcTanh[a*x]^(n+1),x] + 
  a*(m+2*p+2)/(n+1)*Int[x^(m+1)*(c+d*x^2)^p*ArcTanh[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n,p] && p<-1 && n<-1 && NonzeroQ[m+2*p+2]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  x^m*(c+d*x^2)^(p+1)*ArcCoth[a*x]^(n+1)/(a*c*(n+1)) - 
  m/(a*(n+1))*Int[x^(m-1)*(c+d*x^2)^p*ArcCoth[a*x]^(n+1),x] + 
  a*(m+2*p+2)/(n+1)*Int[x^(m+1)*(c+d*x^2)^p*ArcCoth[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m,n,p] && p<-1 && n<-1 && NonzeroQ[m+2*p+2]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcTanh[a_.*x_]^n_.,x_Symbol] :=
  Defer[Int][x^m*(c+d*x^2)^p*ArcTanh[a*x]^n,x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[a^2*c+d]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
  Defer[Int][x^m*(c+d*x^2)^p*ArcCoth[a*x]^n,x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[a^2*c+d]


Int[ArcTanh[u_]*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*ArcTanh[a*x]^n/(c+d*x^2),x] -
  1/2*Int[Log[1-u]*ArcTanh[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+a*x))^2]


Int[ArcCoth[u_]*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*ArcCoth[a*x]^n/(c+d*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*ArcCoth[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+a*x))^2]


Int[ArcTanh[u_]*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*ArcTanh[a*x]^n/(c+d*x^2),x] -
  1/2*Int[Log[1-u]*ArcTanh[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-a*x))^2]


Int[ArcCoth[u_]*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*ArcCoth[a*x]^n/(c+d*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*ArcCoth[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-a*x))^2]


Int[Log[u_]*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  PolyLog[2,Together[1-u]]*ArcTanh[a*x]^n/(2*a*c) -
  n/2*Int[ArcTanh[a*x]^(n-1)*PolyLog[2,Together[1-u]]/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1+a*x))^2]


Int[Log[u_]*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  PolyLog[2,Together[1-u]]*ArcCoth[a*x]^n/(2*a*c) -
  n/2*Int[PolyLog[2,Together[1-u]]*ArcCoth[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1+a*x))^2]


Int[Log[u_]*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  -PolyLog[2,Together[1-u]]*ArcTanh[a*x]^n/(2*a*c) +
  n/2*Int[PolyLog[2,Together[1-u]]*ArcTanh[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1-a*x))^2]


Int[Log[u_]*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  -PolyLog[2,Together[1-u]]*ArcCoth[a*x]^n/(2*a*c) +
  n/2*Int[PolyLog[2,Together[1-u]]*ArcCoth[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1-a*x))^2]


Int[PolyLog[p_,u_]*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  -PolyLog[p+1,u]*ArcTanh[a*x]^n/(2*a*c) +
  n/2*Int[PolyLog[p+1,u]*ArcTanh[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+a*x))^2]


Int[PolyLog[p_,u_]*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  -PolyLog[p+1,u]*ArcCoth[a*x]^n/(2*a*c) +
  n/2*Int[PolyLog[p+1,u]*ArcCoth[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+a*x))^2]


Int[PolyLog[p_,u_]*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  PolyLog[p+1,u]*ArcTanh[a*x]^n/(2*a*c) -
  n/2*Int[PolyLog[p+1,u]*ArcTanh[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-a*x))^2]


Int[PolyLog[p_,u_]*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  PolyLog[p+1,u]*ArcCoth[a*x]^n/(2*a*c) -
  n/2*Int[PolyLog[p+1,u]*ArcCoth[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-a*x))^2]


Int[1/(ArcCoth[a_.*x_]*ArcTanh[a_.*x_]*(c_+d_.*x_^2)),x_Symbol] :=
  (-Log[ArcCoth[a*x]]+Log[ArcTanh[a*x]])/(a*c*ArcCoth[a*x]-a*c*ArcTanh[a*x]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]


Int[ArcCoth[a_.*x_]^m_.*ArcTanh[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  ArcCoth[a*x]^(m+1)*ArcTanh[a*x]^n/(a*c*(m+1)) -
  n/(m+1)*Int[ArcCoth[a*x]^(m+1)*ArcTanh[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n] && 0<n<=m


Int[ArcTanh[a_.*x_]^m_.*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  ArcTanh[a*x]^(m+1)*ArcCoth[a*x]^n/(a*c*(m+1)) -
  n/(m+1)*Int[ArcTanh[a*x]^(m+1)*ArcCoth[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n] && 0<n<m


Int[ArcTanh[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+a*x]/(c+d*x^n),x] -
  1/2*Int[Log[1-a*x]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[a^2*c+d]]


Int[ArcCoth[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+1/(a*x)]/(c+d*x^n),x] -
  1/2*Int[Log[1-1/(a*x)]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[a^2*c+d]]


Int[ArcTanh[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcTanh[a+b*x]/b + Log[1-(a+b*x)^2]/(2*b) /;
FreeQ[{a,b},x]


Int[ArcCoth[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcCoth[a+b*x]/b + Log[1-(a+b*x)^2]/(2*b) /;
FreeQ[{a,b},x]


Int[ArcTanh[a_+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[ArcTanh[x]^n,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1


Int[ArcCoth[a_+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[ArcCoth[x]^n,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1


Int[ArcTanh[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][ArcTanh[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcCoth[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][ArcCoth[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcTanh[a_.+b_.*x_]/x_,x_Symbol] :=
  1/2*Int[Log[1+a+b*x]/x,x] -
  1/2*Int[Log[1-a-b*x]/x,x] /;
FreeQ[{a,b},x]


Int[ArcCoth[a_.+b_.*x_]/x_,x_Symbol] :=
  1/2*Int[Log[1+1/(a+b*x)]/x,x] -
  1/2*Int[Log[1-1/(a+b*x)]/x,x] /;
FreeQ[{a,b},x]


Int[x_^m_.*ArcTanh[a_+b_.*x_],x_Symbol] :=
  x^(m+1)*ArcTanh[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)/(1-a^2-2*a*b*x-b^2*x^2),x] /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]


Int[x_^m_.*ArcCoth[a_+b_.*x_],x_Symbol] :=
  x^(m+1)*ArcCoth[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)/(1-a^2-2*a*b*x-b^2*x^2),x] /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]


Int[x_^m_.*ArcTanh[a_+b_.*x_]^n_,x_Symbol] :=
  1/b^(m+1)*Subst[Int[(x-a)^m*ArcTanh[x]^n,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1 && PositiveIntegerQ[m]


Int[x_^m_.*ArcCoth[a_+b_.*x_]^n_,x_Symbol] :=
  1/b^(m+1)*Subst[Int[(x-a)^m*ArcCoth[x]^n,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1 && PositiveIntegerQ[m]


Int[x_^m_.*ArcTanh[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcTanh[a+b*x]^n,x] /;
FreeQ[{a,b,m},x] && IntegerQ[n] && n>1 && Not[PositiveIntegerQ[m]]


Int[x_^m_.*ArcCoth[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcCoth[a+b*x]^n,x] /;
FreeQ[{a,b,m},x] && IntegerQ[n] && n>1 && Not[PositiveIntegerQ[m]]


Int[x_^m_.*ArcTanh[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcTanh[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*ArcCoth[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcCoth[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcTanh[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+a+b*x]/(c+d*x^n),x] -
  1/2*Int[Log[1-a-b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcCoth[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[(1+a+b*x)/(a+b*x)]/(c+d*x^n),x] -
  1/2*Int[Log[(-1+a+b*x)/(a+b*x)]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcTanh[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcTanh[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcCoth[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcCoth[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcTanh[a_+b_.*x_^n_],x_Symbol] :=
  x*ArcTanh[a+b*x^n] -
  b*n*Int[x^n/(1-a^2-2*a*b*x^n-b^2*x^(2*n)),x] /;
FreeQ[{a,b,n},x]


Int[ArcCoth[a_+b_.*x_^n_],x_Symbol] :=
  x*ArcCoth[a+b*x^n] -
  b*n*Int[x^n/(1-a^2-2*a*b*x^n-b^2*x^(2*n)),x] /;
FreeQ[{a,b,n},x]


Int[ArcTanh[a_.+b_.*x_^n_.]/x_,x_Symbol] :=
  1/2*Int[Log[1+a+b*x^n]/x,x] -
  1/2*Int[Log[1-a-b*x^n]/x,x] /;
FreeQ[{a,b,n},x]


Int[ArcCoth[a_.+b_.*x_^n_.]/x_,x_Symbol] :=
  1/2*Int[Log[1+1/(a+b*x^n)]/x,x] -
  1/2*Int[Log[1-1/(a+b*x^n)]/x,x] /;
FreeQ[{a,b,n},x]


Int[x_^m_.*ArcTanh[a_+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*ArcTanh[a+b*x^n]/(m+1) - 
  b*n/(m+1)*Int[x^(m+n)/(1-a^2-2*a*b*x^n-b^2*x^(2*n)),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n


Int[x_^m_.*ArcCoth[a_+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*ArcCoth[a+b*x^n]/(m+1) - 
  b*n/(m+1)*Int[x^(m+n)/(1-a^2-2*a*b*x^n-b^2*x^(2*n)),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n


Int[ArcTanh[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  1/2*Int[Log[1+a+b*f^(c+d*x)],x] - 
  1/2*Int[Log[1-a-b*f^(c+d*x)],x] /;
FreeQ[{a,b,c,d,f},x] 


Int[ArcCoth[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  1/2*Int[Log[1+1/(a+b*f^(c+d*x))],x] - 
  1/2*Int[Log[1-1/(a+b*f^(c+d*x))],x] /;
FreeQ[{a,b,c,d,f},x] 


Int[x_^m_.*ArcTanh[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  1/2*Int[x^m*Log[1+a+b*f^(c+d*x)],x] - 
  1/2*Int[x^m*Log[1-a-b*f^(c+d*x)],x] /;
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0


Int[x_^m_.*ArcCoth[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  1/2*Int[x^m*Log[1+1/(a+b*f^(c+d*x))],x] - 
  1/2*Int[x^m*Log[1-1/(a+b*f^(c+d*x))],x] /;
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0


Int[u_.*ArcTanh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCoth[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCoth[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcTanh[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  1/c*Log[ArcTanh[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && ZeroQ[b-c^2]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  -1/c*Log[ArcCoth[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && ZeroQ[b-c^2]


Int[ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  ArcTanh[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && ZeroQ[b-c^2] && NonzeroQ[m+1]


Int[ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  -ArcCoth[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && ZeroQ[b-c^2] && NonzeroQ[m+1]


Int[ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcTanh[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b-c^2] && ZeroQ[b*d-a*e]


Int[ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcCoth[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b-c^2] && ZeroQ[b*d-a*e]


Int[E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[a,x] && RationalQ[n]


Int[E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  4*(1-a*x)*E^(n*ArcTanh[a*x])/(a*(n-2)*(1+a*x))*Hypergeometric2F1[2,1-n/2,2-n/2,-E^(-2*ArcTanh[a*x])] /;
FreeQ[{a,n},x] && Not[RationalQ[n]]


Int[x_^m_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[x^m*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,m,n},x]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1+d*x/c)^p*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2-d^2] && (IntegerQ[p] || PositiveQ[c])


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(1+d*x/c)^p*Int[u*(1+d*x/c)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2-d^2] && Not[IntegerQ[p] || PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  d^p*Int[u*(1+c*x/d)^p*E^(n*ArcTanh[a*x])/x^p,x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[c^2-a^2*d^2] && IntegerQ[p]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*c^p*Int[u*(1+d/(c*x))^p*(1+1/(a*x))^(n/2)/(1-1/(a*x))^(n/2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[u*(c+d/x)^p*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  x^p*(c+d/x)^p/(1+c*x/d)^p*Int[u*(1+c*x/d)^p*E^(n*ArcTanh[a*x])/x^p,x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[p]]


Int[E^(n_.*ArcTanh[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcTanh[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]]


Int[E^(n_.*ArcTanh[a_.*x_])/Sqrt[1+d_.*x_^2],x_Symbol] :=
  Int[1/(1-a*n*x),x] /;
FreeQ[{a,d,n},x] && ZeroQ[d+a^2] && ZeroQ[n^2-1]


Int[E^(n_.*ArcTanh[a_.*x_])/Sqrt[c_.+d_.*x_^2],x_Symbol] :=
  Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[E^(n*ArcTanh[a*x])/Sqrt[1-a^2*x^2],x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-1] && NonzeroQ[c-1]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*a*p*x)*(c+d*x^2)^p*E^(n*ArcTanh[a*x])/(2*a*p*(2*p+1)) /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-4*p^2] && NonzeroQ[p+1/2] && Not[IntegerQ[n]]


(* Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*a*p*x)*(c+d*x^2)^p*E^(n*ArcTanh[a*x])/(2*a*p*(2*p+1)) - 
  c*(n^2-4*p^2)/(2*p*(2*p+1))*Int[(c+d*x^2)^(p-1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n^2-4*p^2] && RationalQ[p] && p>0 *)


Int[E^(n_.*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  1/c^(3/2)*Int[1/((1+a*n*x)*(1-a*n*x)^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-1] && PositiveQ[c]


Int[E^(n_.*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  Sqrt[1-a^2*x^2]/(c*Sqrt[c+d*x^2])*Int[E^(n*ArcTanh[a*x])/(1-a^2*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-1] && Not[PositiveQ[c]]


Int[E^(n_*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n-a*x)*E^(n*ArcTanh[a*x])/(a*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n^2-9] && NonzeroQ[n^2-1]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a*c*(n^2-4*(p+1)^2)) - 
  2*(p+1)*(2*p+3)/(c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n^2-4*p^2] && RationalQ[p] && p<-1 && p!=-3/2 && NonzeroQ[n^2-4*(p+1)^2] && 
  Not[IntegerQ[n]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-a^2*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c]) && OddQ[n]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c]) && Not[OddQ[n]] && 
  (RationalQ[n,p] || PositiveIntegerQ[p-n/2] || PositiveIntegerQ[p+n/2])


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(n/2)*Int[(c+d*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[p] || PositiveQ[c]] && EvenQ[n] && RationalQ[p]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && PositiveIntegerQ[p+1/2] && RationalQ[n]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && NegativeIntegerQ[p-1/2] && RationalQ[n]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(1-a^2*x^2)^p*Int[(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[p+1/2]] && 
  (RationalQ[n,p] || PositiveIntegerQ[p-n/2] || PositiveIntegerQ[p+n/2])


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(2*a*c*n)*(1+E^(n/(p+1)*ArcTanh[a*x]))^(2*(p+1))*
    Hypergeometric2F1[2*(p+1),2*(p+1),2*p+3,-E^(n/(p+1)*ArcTanh[a*x])] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-4*(p+1)^2] && Not[IntegerQ[2*p]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  4^(p+1)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a*c*(n-2*(p+1)))*(1/(1+a*x))^(2*(p+1))*
    Hypergeometric2F1[p-n/2+1,2*(p+1),p-n/2+2,-E^(-2*ArcTanh[a*x])] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && NonzeroQ[n^2-4*(p+1)^2] && Not[NegativeIntegerQ[2*p+1]] && Not[IntegerQ[p-n/2]]


Int[x_*E^(n_*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcTanh[a*x])/(a^2*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a^2*c*(n^2-4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p<=-1 && p!=-3/2 && NonzeroQ[n^2-4*(p+1)^2] && Not[IntegerQ[n]]


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  -(n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a^3*c*n^2*(n^2-1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2+2*(p+1)] && Not[IntegerQ[n]]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a^3*c*(n^2-4*(p+1)^2)) - 
  (n^2+2*(p+1))/(a^2*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p<=-1 && NonzeroQ[n^2+2*(p+1)] && NonzeroQ[n^2-4*(p+1)^2] && Not[IntegerQ[n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p/a^(m+1)*Subst[Int[E^(n*x)*Tanh[x]^(m+2*(p+1))/Sinh[x]^(2*(p+1)),x],x,ArcTanh[a*x]] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && IntegerQ[m] && RationalQ[p] && 3<=m<=-2(p+1) && IntegerQ[p] && Not[IntegerQ[n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1-a^2*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c]) && OddQ[n] && 
  (Not[RationalQ[p]] || Not[RationalQ[m]] || ZeroQ[n-1] && NonzeroQ[p+1]) && Not[IntegerQ[p-n/2]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(n/2)*Int[x^m*(c+d*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[p] || PositiveQ[c]] && IntegerQ[n/2] && (ZeroQ[m-1] || Not[IntegerQ[p+1/2]])


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c])


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/(Sqrt[1-a*x]*Sqrt[1+a*x])*Int[u*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && IntegerQ[n/2] && PositiveIntegerQ[p+1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1-a*x]*Sqrt[1+a*x]/Sqrt[c+d*x^2]*Int[u*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && IntegerQ[n/2] && NegativeIntegerQ[p-1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[u*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && Not[IntegerQ[n/2]] && PositiveIntegerQ[p+1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[u*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && Not[IntegerQ[n/2]] && NegativeIntegerQ[p-1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(1-a^2*x^2)^p*Int[u*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[n/2]] && Not[IntegerQ[p+1/2]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^(2*p)*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[c+a^2*d] && IntegerQ[p]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-1/(a*x))^p*(1+1/(a*x))^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[p]] && IntegerQ[n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/((1-a*x)^p*(1+a*x)^p)*Int[u/x^(2*p)*(1-a*x)^p*(1+a*x)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[p]] && IntegerQ[n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/(1+c*x^2/d)^p*Int[u/x^(2*p)*(1+c*x^2/d)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[p]] && Not[IntegerQ[n/2]]


Int[u_.*E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*Int[u*E^(n*ArcTanh[a*x]),x] /;
FreeQ[a,x] && IntegerQ[n/2]


Int[E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^(n/2)/(x^2*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[a,x] && Not[IntegerQ[n/2]]


Int[x_^m_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[n/2]] && IntegerQ[m]


Int[x_^m_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -x^m*(1/x)^m*Subst[Int[(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[n/2]] && Not[IntegerQ[m]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c^2-d^2] && Not[IntegerQ[n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(x^p*(1+c/(d*x))^p)*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2-d^2] && Not[IntegerQ[n/2]] && Not[IntegerQ[p]]


Int[(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^2*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c])


Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegerQ[m]


Int[x_^m_*(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[u*(1+d/(c*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcCoth[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcCoth[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]]


Int[E^(n_*ArcCoth[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n-a*x)*E^(n*ArcCoth[a*x])/(a*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a*c*(n^2-4*(p+1)^2)) - 
  2*(p+1)*(2*p+3)/(c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && RationalQ[p] && p<-1 && p!=-3/2 && NonzeroQ[n^2-4*(p+1)^2] && 
  (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_*E^(n_*ArcCoth[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcCoth[a*x])/(a^2*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^2*c*(n^2-4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && RationalQ[p] && p<=-1 && p!=-3/2 && NonzeroQ[n^2-4*(p+1)^2] && 
  (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^3*c*n^2*(n^2-1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && ZeroQ[n^2+2*(p+1)] && NonzeroQ[n^2-1]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^3*c*(n^2-4*(p+1)^2)) - 
  (n^2+2*(p+1))/(a^2*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && RationalQ[p] && p<=-1 && NonzeroQ[n^2+2*(p+1)] && 
  NonzeroQ[n^2-4*(p+1)^2] && (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(-c)^p/a^(m+1)*Subst[Int[E^(n*x)*Coth[x]^(m+2*(p+1))/Cosh[x]^(2*(p+1)),x],x,ArcCoth[a*x]] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && IntegerQ[m] && RationalQ[p] && 3<=m<=-2(p+1) && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^(2*p)*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(x^(2*p)*(1-1/(a^2*x^2))^p)*Int[u*x^(2*p)*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && Not[IntegerQ[p]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  c^p/a^(2*p)*Int[u/x^(2*p)*(-1+a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegersQ[2*p,p+n/2]


Int[(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^2,x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+n/2]]


Int[x_^m_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+n/2]] && 
  IntegerQ[m]


Int[x_^m_*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+n/2]] && 
  Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d/x^2)^p/(1-1/(a^2*x^2))^p*Int[u*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(1+a*c+b*c*x)^(n/2)/(1-a*c-b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,n},x]


Int[x_^m_*E^(n_*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/n)*(-1-a*c+(1-a*c)*x^(2/n))^m/(1+x^(2/n))^(m+2),x],x,(1+c*(a+b*x))^(n/2)/(1-c*(a+b*x))^(n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[n] && -1<n<1


Int[x_^m_.*E^(n_.*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[x^m*(1+a*c+b*c*x)^(n/2)/(1-a*c-b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,m,n},x] && Not[NegativeIntegerQ[m] && RationalQ[n] && -1<n<1]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTanh[a_+b_.*x_]),x_Symbol] :=
  (c/(1-a^2))^p*Int[u*(1-a-b*x)^(p-n/2)*(1+a+b*x)^(p+n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c+e(1-a^2)] && (IntegerQ[p] || PositiveQ[c/(1-a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTanh[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1-a^2-2*a*b*x-b^2*x^2)^p*Int[u*(1-a^2-2*a*b*x-b^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c+e(1-a^2)] && Not[IntegerQ[p] || PositiveQ[c/(1-a^2)]]


Int[u_.*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (-1)^(n/2)*Int[u*E^(n*ArcTanh[c*(a+b*x)]),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n/2]


Int[E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (c*(a+b*x))^(n/2)*(1+1/(c*(a+b*x)))^(n/2)/(1+a*c+b*c*x)^(n/2)*Int[(1+a*c+b*c*x)^(n/2)/(-1+a*c+b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n/2]]


Int[x_^m_*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  -4/(n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/n)*(1+a*c+(1-a*c)*x^(2/n))^m/(-1+x^(2/n))^(m+2),x],x,(1+1/(c*(a+b*x)))^(n/2)/(1-1/(c*(a+b*x)))^(n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[n] && -1<n<1


Int[x_^m_.*E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (c*(a+b*x))^(n/2)*(1+1/(c*(a+b*x)))^(n/2)/(1+a*c+b*c*x)^(n/2)*Int[x^m*(1+a*c+b*c*x)^(n/2)/(-1+a*c+b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[n/2]] && Not[NegativeIntegerQ[m] && RationalQ[n] && -1<n<1]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCoth[a_+b_.*x_]),x_Symbol] :=
  (c/(1-a^2))^p*((a+b*x)/(1+a+b*x))^(n/2)*((1+a+b*x)/(a+b*x))^(n/2)*((1-a-b*x)^(n/2)/(-1+a+b*x)^(n/2))*
    Int[u*(1-a-b*x)^(p-n/2)*(1+a+b*x)^(p+n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[n/2]] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c+e(1-a^2)] && (IntegerQ[p] || PositiveQ[c/(1-a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCoth[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1-a^2-2*a*b*x-b^2*x^2)^p*Int[u*(1-a^2-2*a*b*x-b^2*x^2)^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[n/2]] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c+e(1-a^2)] && 
  Not[IntegerQ[p] || PositiveQ[c/(1-a^2)]]


Int[u_.*E^(n_.*ArcTanh[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcCoth[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*E^(n_.*ArcCoth[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcTanh[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[(c_.+d_.*x_^2)^n_*ArcTanh[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcTanh[a*x],u,x] - 
  a*Int[Dist[1/(1-a^2*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[2*n] && n<=-1


Int[(c_.+d_.*x_^2)^n_*ArcCoth[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcCoth[a*x],u,x] - 
  a*Int[Dist[1/(1-a^2*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[2*n] && n<=-1


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcTanh[a+b*x]]/(1-(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Tanh[x]/b,x],x],x,ArcTanh[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sech[x]^(2*(n+1)),x],x], x, tmp]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTanh && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sech[x]^(2*(n+1)),x],x], x, tmp] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTanh && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcCoth[a+b*x]]/(1-(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Coth[x]/b,x],x],x,ArcCoth[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*(-Csch[x]^2)^(n+1),x],x], x, tmp]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCoth && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*(-Csch[x]^2)^(n+1),x],x], x, tmp] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCoth && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


Int[ArcTanh[u_],x_Symbol] :=
  x*ArcTanh[u] - 
  Int[SimplifyIntegrand[x*D[u,x]/(1-u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[ArcCoth[u_],x_Symbol] :=
  x*ArcCoth[u] - 
  Int[SimplifyIntegrand[x*D[u,x]/(1-u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[x_^m_.*ArcTanh[u_],x_Symbol] :=
  x^(m+1)*ArcTanh[u]/(m+1) - 
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/(1-u^2),x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	FalseQ[PowerVariableExpn[u,m+1,x]]


Int[x_^m_.*ArcCoth[u_],x_Symbol] :=
  x^(m+1)*ArcCoth[u]/(m+1) - 
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/(1-u^2),x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	FalseQ[PowerVariableExpn[u,m+1,x]]


Int[v_*ArcTanh[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[ArcTanh[u],w,x] -
  Int[SimplifyIntegrand[w*D[u,x]/(1-u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x] && 
	Not[MatchQ[v, x^m_. /; FreeQ[m,x]]] &&
	FalseQ[FunctionOfLinear[v*ArcTanh[u],x]]


Int[v_*ArcCoth[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[ArcCoth[u],w,x] -
  Int[SimplifyIntegrand[w*D[u,x]/(1-u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x] && 
	Not[MatchQ[v, x^m_. /; FreeQ[m,x]]] &&
	FalseQ[FunctionOfLinear[v*ArcCoth[u],x]]


Int[ArcSech[a_.*x_],x_Symbol] :=
  x*ArcSech[a*x] + Int[Sqrt[(1-a*x)/(1+a*x)]/(1-a*x),x] /;
FreeQ[a,x]


Int[ArcCsch[a_.*x_],x_Symbol] :=
  x*ArcCsch[a*x] + 1/a*Int[1/(x*Sqrt[1+1/(a^2*x^2)]),x] /;
FreeQ[a,x]


Int[ArcSech[a_.*x_]^n_,x_Symbol] :=
  -1/a*Subst[Int[x^n*Sech[x]*Tanh[x],x],x,ArcSech[a*x]] /;
FreeQ[{a,n},x]


Int[ArcCsch[a_.*x_]^n_,x_Symbol] :=
  -1/a*Subst[Int[x^n*Csch[x]*Cot[x],x],x,ArcCsch[a*x]] /;
FreeQ[{a,n},x]


Int[ArcSech[a_.*x_]/x_,x_Symbol] :=
  -1/2*ArcSech[a*x]^2 - 
  ArcSech[a*x]*Log[2*(1-Sqrt[(1-a*x)/(1+a*x)]*(1+a*x))/(a^2*x^2)] + 
  1/2*PolyLog[2,1-2*(1-Sqrt[(1-a*x)/(1+a*x)]*(1+a*x))/(a^2*x^2)] /;
FreeQ[a,x]


Int[ArcCsch[a_.*x_]/x_,x_Symbol] :=
  -1/2*ArcCsch[a*x]^2 - 
  ArcCsch[a*x]*Log[-2*(1-a*Sqrt[1+1/(a^2*x^2)]*x)/(a^2*x^2)] + 
  1/2*PolyLog[2,1+2*(1-a*Sqrt[1+1/(a^2*x^2)]*x)/(a^2*x^2)] /;
FreeQ[a,x]


Int[x_^m_.*ArcSech[a_.*x_],x_Symbol] :=
  x^(m+1)*ArcSech[a*x]/(m+1) + 
  1/(m+1)*Int[x^m/(Sqrt[(1-a*x)/(1+a*x)]*(1+a*x)),x] /;
FreeQ[{a,m},x] && NonzeroQ[m+1]


Int[x_^m_.*ArcCsch[a_.*x_],x_Symbol] :=
  x^(m+1)*ArcCsch[a*x]/(m+1) + 
  1/(a*(m+1))*Int[x^(m-1)/Sqrt[1+1/(a^2*x^2)],x] /;
FreeQ[{a,m},x] && NonzeroQ[m+1]


Int[x_^m_.*ArcSech[a_.*x_]^n_,x_Symbol] :=
  -1/a^(m+1)*Subst[Int[x^n*Sech[x]^(m+1)*Tanh[x],x],x,ArcSech[a*x]] /;
FreeQ[{a,n},x] && IntegerQ[m]


Int[x_^m_.*ArcCsch[a_.*x_]^n_,x_Symbol] :=
  -1/a^(m+1)*Subst[Int[x^n*Csch[x]^(m+1)*Coth[x],x],x,ArcCsch[a*x]] /;
FreeQ[{a,n},x] && IntegerQ[m]


Int[ArcSech[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcSech[a+b*x]/b + 
  Int[Sqrt[(1-a-b*x)/(1+a+b*x)]/(1-a-b*x),x] /;
FreeQ[{a,b},x]


Int[ArcCsch[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcCsch[a+b*x]/b + 
  Int[1/((a+b*x)*Sqrt[1+1/(a+b*x)^2]),x] /;
FreeQ[{a,b},x]


Int[ArcSech[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[x^n*Sech[x]*Tanh[x],x],x,ArcSech[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcCsch[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[x^n*Csch[x]*Coth[x],x],x,ArcCsch[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcSech[a_+b_.*x_]/x_,x_Symbol] :=
  -ArcSech[a+b*x]*Log[1+E^(-2*ArcSech[a+b*x])] + 
  ArcSech[a+b*x]*Log[1-(1-Sqrt[1-a^2])/(E^ArcSech[a+b*x]*a)] + 
  ArcSech[a+b*x]*Log[1-(1+Sqrt[1-a^2])/(E^ArcSech[a+b*x]*a)] + 
  1/2*PolyLog[2,-E^(-2*ArcSech[a+b*x])] - 
  PolyLog[2,(1-Sqrt[1-a^2])/(E^ArcSech[a+b*x]*a)] - 
  PolyLog[2,(1+Sqrt[1-a^2])/(E^ArcSech[a+b*x]*a)] /;
FreeQ[{a,b},x]


Int[ArcCsch[a_+b_.*x_]/x_,x_Symbol] :=
  -ArcCsch[a+b*x]^2 - 
  ArcCsch[a+b*x]*Log[1-E^(-2*ArcCsch[a+b*x])] + 
  ArcCsch[a+b*x]*Log[1+(1-Sqrt[1+a^2])*E^ArcCsch[a+b*x]/a] + 
  ArcCsch[a+b*x]*Log[1+(1+Sqrt[1+a^2])*E^ArcCsch[a+b*x]/a] + 
  1/2*PolyLog[2,E^(-2*ArcCsch[a+b*x])] + 
  PolyLog[2,-(1-Sqrt[1+a^2])*E^ArcCsch[a+b*x]/a] + 
  PolyLog[2,-(1+Sqrt[1+a^2])*E^ArcCsch[a+b*x]/a] /;
FreeQ[{a,b},x]


Int[x_^m_.*ArcSech[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcSech[a+b*x]/(b^(m+1)*(m+1)) - 
  1/(b^(m+1)*(m+1))*Subst[Int[(((-a)*x)^(m+1)-(1-a*x)^(m+1))*Sqrt[(-1+x)/(1+x)]/(x^(m+1)*(1-x)),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NonzeroQ[m+1]


Int[x_^m_.*ArcCsch[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcCsch[a+b*x]/(b^(m+1)*(m+1)) + 
  1/(b^(m+1)*(m+1))*Subst[Int[(((-a)*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1+x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NonzeroQ[m+1]


Int[x_^m_.*ArcSech[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b^(m+1)*Subst[Int[x^n*(-a+Sech[x])^m*Sech[x]*Tanh[x],x],x,ArcSech[a+b*x]] /;
FreeQ[{a,b,n},x] && IntegerQ[m]


Int[x_^m_.*ArcCsch[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b^(m+1)*Subst[Int[x^n*(-a+Csch[x])^m*Csch[x]*Coth[x],x],x,ArcCsch[a+b*x]] /;
FreeQ[{a,b,n},x] && PositiveIntegerQ[m]


Int[u_.*ArcSech[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCosh[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCsch[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSinh[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


(* Int[ArcSech[u_],x_Symbol] :=
  x*ArcSech[u] +
  Int[SimplifyIntegrand[x*D[u,x]/(u^2*Sqrt[-1+1/u]*Sqrt[1+1/u]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]] *)


Int[ArcCsch[u_],x_Symbol] :=
  x*ArcCsch[u] +
  Int[SimplifyIntegrand[x*D[u,x]/(u^2*Sqrt[1+1/u^2]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[E^ArcSech[a_.*x_^p_.], x_Symbol] :=
  x*E^ArcSech[a*x^p] + p/a*Int[1/x^p,x] + p/a*Int[1/(x^p*(1-a*x^p))*Sqrt[(1-a*x^p)/(1+a*x^p)],x] /;
FreeQ[{a,p},x]


Int[E^(n_.*ArcSech[u_]), x_Symbol] :=
  Int[(1/u + Sqrt[(1-u)/(1+u)] + 1/u*Sqrt[(1-u)/(1+u)])^n,x] /;
IntegerQ[n]


Int[E^ArcSech[a_.*x_^p_.]/x_, x_Symbol] :=
(*-1/(a*p*x^p) + 1/a*Int[(1+a*x^p)/x^(p+1)*Sqrt[(1-a*x^p)/(1+a*x^p)],x] /; *)
  -1/(a*p*x^p) + Int[1/x*Sqrt[(1-a*x^p)/(1+a*x^p)],x] + 1/a*Int[1/x^(p+1)*Sqrt[(1-a*x^p)/(1+a*x^p)],x] /;
FreeQ[{a,p},x]


Int[x_^m_.*E^ArcSech[a_.*x_^p_.], x_Symbol] :=
  x^(m+1)*E^ArcSech[a*x^p]/(m+1) + 
  p/(a*(m+1))*Int[x^(m-p),x] + 
  p/(a*(m+1))*Int[x^(m-p)/(1-a*x^p)*Sqrt[(1-a*x^p)/(1+a*x^p)],x] /;
FreeQ[{a,m,p},x] && NonzeroQ[m+1]


Int[x_^m_.*E^(n_.*ArcSech[u_]), x_Symbol] :=
  Int[x^m*(1/u + Sqrt[(1-u)/(1+u)] + 1/u*Sqrt[(1-u)/(1+u)])^n,x] /;
FreeQ[m,x] && IntegerQ[n]


Int[E^ArcCsch[a_.*x_^p_.], x_Symbol] :=
  x*E^ArcCsch[a*x^p] + p/a*Int[1/x^p,x] + p*Int[1/(1+a^2*x^(2*p))*Sqrt[(1+a^2*x^(2*p))/(a^2*x^(2*p))],x] /;
FreeQ[{a,p},x]


Int[E^(n_.*ArcCsch[u_]), x_Symbol] :=
  Int[(1/u + Sqrt[1+1/u^2])^n,x] /;
IntegerQ[n]


Int[E^ArcCsch[a_.*x_^p_.]/x_, x_Symbol] :=
  -1/(a*p*x^p) + Int[1/x*Sqrt[(1+a^2*x^(2*p))/(a^2*x^(2*p))],x] /;
FreeQ[{a,p},x]


Int[x_^m_.*E^ArcCsch[a_.*x_^p_.], x_Symbol] :=
  x^(m+1)*E^ArcCsch[a*x^p]/(m+1) + 
  p/(a*(m+1))*Int[x^(m-p),x] + 
  p/(m+1)*Int[x^m/(1+a^2*x^(2*p))*Sqrt[(1+a^2*x^(2*p))/(a^2*x^(2*p))],x] /;
FreeQ[{a,m,p},x] && PositiveIntegerQ[m]


Int[x_^m_.*E^(n_.*ArcCsch[u_]), x_Symbol] :=
  Int[x^m*(1/u + Sqrt[1+1/u^2])^n,x] /;
FreeQ[m,x] && IntegerQ[n]
