(* ::Package:: *)

Int[ArcSin[c_.+d_.*x_],x_Symbol] :=
  (c+d*x)*ArcSin[c+d*x]/d + Sqrt[1-(c+d*x)^2]/d /;
FreeQ[{c,d},x]


Int[ArcCos[c_.+d_.*x_],x_Symbol] :=
  (c+d*x)*ArcCos[c+d*x]/d - Sqrt[1-(c+d*x)^2]/d /;
FreeQ[{c,d},x]


Int[(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcSin[c+d*x])^n/d - 
  b*n*Int[(c+d*x)*(a+b*ArcSin[c+d*x])^(n-1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && 0<n<1


Int[(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcCos[c+d*x])^n/d + 
  b*n*Int[(c+d*x)*(a+b*ArcCos[c+d*x])^(n-1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && 0<n<1


Int[(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcSin[c+d*x])^n/d + 
  b*n*Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])^(n-1)/d - 
  b^2*n*(n-1)*Int[(a+b*ArcSin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1


Int[(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcCos[c+d*x])^n/d - 
  b*n*Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])^(n-1)/d - 
  b^2*n*(n-1)*Int[(a+b*ArcCos[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1


Int[1/(a_.+b_.*ArcSin[c_.+d_.*x_])^2,x_Symbol] :=
  -Sqrt[1-(c+d*x)^2]/(b*d*(a+b*ArcSin[c+d*x])) - 
  1/b*Int[(c+d*x)/(Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(a_.+b_.*ArcCos[c_.+d_.*x_])^2,x_Symbol] :=
  Sqrt[1-(c+d*x)^2]/(b*d*(a+b*ArcCos[c+d*x])) + 
  1/b*Int[(c+d*x)/(Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(a_.+b_.*ArcSin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*Sqrt[1-(c+d*x)^2]/(b*d*Sqrt[a+b*ArcSin[c+d*x]]) - 
  2/b*Int[(c+d*x)/(Sqrt[1-(c+d*x)^2]*Sqrt[a+b*ArcSin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(a_.+b_.*ArcCos[c_.+d_.*x_])^(3/2),x_Symbol] :=
  2*Sqrt[1-(c+d*x)^2]/(b*d*Sqrt[a+b*ArcCos[c+d*x]]) + 
  2/b*Int[(c+d*x)/(Sqrt[1-(c+d*x)^2]*Sqrt[a+b*ArcCos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x]


Int[(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcSin[c+d*x])^(n+2)/(b^2*d*(n+1)*(n+2)) + 
  Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])^(n+1)/(b*d*(n+1)) - 
  1/(b^2*(n+1)*(n+2))*Int[(a+b*ArcSin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-2


Int[(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  (c+d*x)*(a+b*ArcCos[c+d*x])^(n+2)/(b^2*d*(n+1)*(n+2)) - 
  Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])^(n+1)/(b*d*(n+1)) - 
  1/(b^2*(n+1)*(n+2))*Int[(a+b*ArcCos[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-2


Int[(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(b*d)*Subst[Int[x^n*Cos[a/b-x/b],x],x,a+b*ArcSin[c+d*x]] /;
FreeQ[{a,b,c,d,n},x]


Int[(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(b*d)*Subst[Int[x^n*Sin[a/b-x/b],x],x,a+b*ArcCos[c+d*x]] /;
FreeQ[{a,b,c,d,n},x]


Int[(a_.+b_.*ArcSin[c_.+d_.*x_])^n_./(e_.+f_.*x_),x_Symbol] :=
  1/f*Subst[Int[(a+b*x)^n*Cot[x],x],x,ArcSin[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCos[c_.+d_.*x_])^n_./(e_.+f_.*x_),x_Symbol] :=
  -1/f*Subst[Int[(a+b*x)^n*Tan[x],x],x,ArcCos[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcSin[c_.+d_.*x_])^n_/(e_.+f_.*x_),x_Symbol] :=
  Defer[Int][(a+b*ArcSin[c+d*x])^n/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && (NonzeroQ[d*e-c*f] || Not[PositiveIntegerQ[n]])


Int[(a_.+b_.*ArcCos[c_.+d_.*x_])^n_/(e_.+f_.*x_),x_Symbol] :=
  Defer[Int][(a+b*ArcCos[c+d*x])^n/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && (NonzeroQ[d*e-c*f] || Not[PositiveIntegerQ[n]])


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcSin[c_.+d_.*x_]),x_Symbol] :=
  f^m/(b*d^(m+1))*Subst[Int[(Sin[x/b-a/b]^m*Cos[x/b-a/b])/x,x],x,a+b*ArcSin[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcCos[c_.+d_.*x_]),x_Symbol] :=
  -f^m/(b*d^(m+1))*Subst[Int[(Cos[x/b-a/b]^m*Sin[x/b-a/b])/x,x],x,a+b*ArcCos[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcSin[c_.+d_.*x_])^2,x_Symbol] :=
  -(e+f*x)^m*Sqrt[1-(c+d*x)^2]/(b*d*(a+b*ArcSin[c+d*x])) + 
  f^m/(b^2*d^(m+1))*Subst[Int[Expand[TrigReduce[Sin[x/b-a/b]^(m-1)*(m-(m+1)*Sin[x/b-a/b]^2)]/x],x],x,a+b*ArcSin[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcCos[c_.+d_.*x_])^2,x_Symbol] :=
  (e+f*x)^m*Sqrt[1-(c+d*x)^2]/(b*d*(a+b*ArcCos[c+d*x])) + 
  f^m/(b^2*d^(m+1))*Subst[Int[Expand[TrigReduce[Cos[x/b-a/b]^(m-1)*(m-(m+1)*Cos[x/b-a/b]^2)]/x],x],x,a+b*ArcCos[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcSin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*(e+f*x)^m*Sqrt[1-(c+d*x)^2]/(b*d*Sqrt[a+b*ArcSin[c+d*x]]) + 
  4*f^m/(b^2*d^(m+1))*Subst[Int[TrigReduce[Sin[x^2/b-a/b]^(m-1)*(m-(m+1)*Sin[x^2/b-a/b]^2)],x],x,Sqrt[a+b*ArcSin[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_./(a_.+b_.*ArcCos[c_.+d_.*x_])^(3/2),x_Symbol] :=
  2*(e+f*x)^m*Sqrt[1-(c+d*x)^2]/(b*d*Sqrt[a+b*ArcCos[c+d*x]]) + 
  4*f^m/(b^2*d^(m+1))*Subst[Int[TrigReduce[Cos[x^2/b-a/b]^(m-1)*(m-(m+1)*Cos[x^2/b-a/b]^2)],x],x,Sqrt[a+b*ArcCos[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)*Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*(a+b*ArcSin[c+d*x])^(n+2)/(d^2*b^2*(n+1)*(n+2)) + 
  2*d/(b*f*(n+1))*Int[(e+f*x)^2*(a+b*ArcSin[c+d*x])^(n+1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && RationalQ[n] && n<-1 && n!=-2


Int[(e_.+f_.*x_)*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(e+f*x)*Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*(a+b*ArcCos[c+d*x])^(n+2)/(d^2*b^2*(n+1)*(n+2)) - 
  2*d/(b*f*(n+1))*Int[(e+f*x)^2*(a+b*ArcCos[c+d*x])^(n+1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && RationalQ[n] && n<-1 && n!=-2


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)^m*Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m*(e+f*x)^(m-1)*(a+b*ArcSin[c+d*x])^(n+2)/(b^2*d^2*(n+1)*(n+2)) + 
  (m+1)*(e+f*x)^(m+1)*(a+b*ArcSin[c+d*x])^(n+2)/(b^2*f*(n+1)*(n+2))  - 
  (m+1)^2/(b^2*(n+1)*(n+2))*Int[(e+f*x)^m*(a+b*ArcSin[c+d*x])^(n+2),x] + 
  f^2*m*(m-1)/(b^2*d^2*(n+1)*(n+2))*Int[(e+f*x)^(m-2)*(a+b*ArcSin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && RationalQ[n] && n<-2 && IntegerQ[m] && m>1


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(e+f*x)^m*Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m*(e+f*x)^(m-1)*(a+b*ArcCos[c+d*x])^(n+2)/(b^2*d^2*(n+1)*(n+2)) + 
  (m+1)*(e+f*x)^(m+1)*(a+b*ArcCos[c+d*x])^(n+2)/(b^2*f*(n+1)*(n+2)) - 
  (m+1)^2/(b^2*(n+1)*(n+2))*Int[(e+f*x)^m*(a+b*ArcCos[c+d*x])^(n+2),x] + 
  f^2*m*(m-1)/(b^2*d^2*(n+1)*(n+2))*Int[(e+f*x)^(m-2)*(a+b*ArcCos[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[d*e-c*f] && RationalQ[n] && n<-2 && IntegerQ[m] && m>1


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcSin[c+d*x])^n/(f*(m+1)) - 
  b*d*n/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcSin[c+d*x])^(n-1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[m+1] && ZeroQ[d*e-c*f] && Not[RationalQ[n] && n<0] && 
  (RationalQ[n] && n>0 || PositiveIntegerQ[m])


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcCos[c+d*x])^n/(f*(m+1)) + 
  b*d*n/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcCos[c+d*x])^(n-1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[m+1] && ZeroQ[d*e-c*f] && Not[RationalQ[n] && n<0] && 
  (RationalQ[n] && n>0 || PositiveIntegerQ[m])


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_]),x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcSin[c+d*x])/(f*(m+1)) - 
  b*d/(f*(m+1))*Int[(e+f*x)^(m+1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[d*e-c*f] && NonzeroQ[m+1]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_]),x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcCos[c+d*x])/(f*(m+1)) + 
  b*d/(f*(m+1))*Int[(e+f*x)^(m+1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[d*e-c*f] && NonzeroQ[m+1]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcSin[c+d*x])^n/(f*(m+1)) - 
  b*d*n/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcSin[c+d*x])^(n-1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m<-1


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcCos[c+d*x])^n/(f*(m+1)) + 
  b*d*n/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcCos[c+d*x])^(n-1)/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m<-1


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+b*ArcSin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[d*e-c*f] && PositiveIntegerQ[m] && NonzeroQ[c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+b*ArcCos[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[d*e-c*f] && PositiveIntegerQ[m] && NonzeroQ[c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/(b*d^(m+1))*Subst[Int[x^n*Cos[x/b-a/b]*(d*e-c*f+f*Sin[x/b-a/b])^m,x],x,a+b*ArcSin[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && IntegerQ[m] && IntegerQ[n] && Not[m<0 && n<0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_.,x_Symbol] :=
  -1/(b*d^(m+1))*Subst[Int[x^n*Sin[x/b-a/b]*(d*e-c*f+f*Cos[x/b-a/b])^m,x],x,a+b*ArcCos[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && IntegerQ[m] && IntegerQ[n] && Not[m<0 && n<0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_,x_Symbol] :=
  2/(b*d^(m+1))*Subst[Int[x^(2*n+1)*Cos[x^2/b-a/b]*(d*e-c*f+f*Sin[x^2/b-a/b])^m,x],x,Sqrt[a+b*ArcSin[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n-1/2]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
  -2/(b*d^(m+1))*Subst[Int[x^(2*n+1)*Sin[x^2/b-a/b]*(d*e-c*f+f*Cos[x^2/b-a/b])^m,x],x,Sqrt[a+b*ArcCos[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n-1/2]


Int[1/(Sqrt[u_]*(a_.+b_.*ArcSin[c_.+d_.*x_])),x_Symbol] :=
  Log[a+b*ArcSin[c+d*x]]/(b*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[u-(1-(c+d*x)^2)]


Int[1/(Sqrt[u_]*(a_.+b_.*ArcCos[c_.+d_.*x_])),x_Symbol] :=
  -Log[a+b*ArcCos[c+d*x]]/(b*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[u-(1-(c+d*x)^2)]


Int[(a_.+b_.*ArcSin[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  (a+b*ArcSin[c+d*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[u-(1-(c+d*x)^2)] && NonzeroQ[n+1]


Int[(a_.+b_.*ArcCos[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  -(a+b*ArcCos[c+d*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[u-(1-(c+d*x)^2)] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  -f*Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])^n/d^2 + 
  b*f*n/d*Int[(a+b*ArcSin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[n] && n>0


Int[(e_.+f_.*x_)*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  -f*Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])^n/d^2 - 
  b*f*n/d*Int[(a+b*ArcCos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[n] && n>0


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  -f*(e+f*x)^(m-1)*Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])^n/(d^2*m) + 
  b*f*n/(d*m)*Int[(e+f*x)^(m-1)*(a+b*ArcSin[c+d*x])^(n-1),x] + 
  f^2*(m-1)/(d^2*m)*Int[(e+f*x)^(m-2)*(a+b*ArcSin[c+d*x])^n/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m>1


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  -f*(e+f*x)^(m-1)*Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])^n/(d^2*m) - 
  b*f*n/(d*m)*Int[(e+f*x)^(m-1)*(a+b*ArcCos[c+d*x])^(n-1),x] + 
  f^2*(m-1)/(d^2*m)*Int[(e+f*x)^(m-2)*(a+b*ArcCos[c+d*x])^n/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m>1


Int[ArcSin[c_.+d_.*x_]/((e_.+f_.*x_)*Sqrt[u_]),x_Symbol] :=
  -2*I*ArcSin[c+d*x]*ArcTan[c+d*x-I*Sqrt[1-(c+d*x)^2]]/f + 
  I*PolyLog[2,-I*(c+d*x)-Sqrt[1-(c+d*x)^2]]/f - 
  I*PolyLog[2,I*(c+d*x)+Sqrt[1-(c+d*x)^2]]/f /;
FreeQ[{c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f]


Int[ArcCos[c_.+d_.*x_]/((e_.+f_.*x_)*Sqrt[u_]),x_Symbol] :=
  2*I*ArcCos[c+d*x]*ArcTan[c+d*x+I*Sqrt[1-(c+d*x)^2]]/f - 
  I*PolyLog[2,-I*(c+d*x)+Sqrt[1-(c+d*x)^2]]/f + 
  I*PolyLog[2,I*(c+d*x)-Sqrt[1-(c+d*x)^2]]/f /;
FreeQ[{c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f]


Int[(a_+b_.*ArcSin[c_.+d_.*x_])/((e_.+f_.*x_)*Sqrt[u_]),x_Symbol] :=
  a*Int[1/((e+f*x)*Sqrt[1-(c+d*x)^2]),x] + 
  b*Int[ArcSin[c+d*x]/((e+f*x)*Sqrt[1-(c+d*x)^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f]


Int[(a_+b_.*ArcCos[c_.+d_.*x_])/((e_.+f_.*x_)*Sqrt[u_]),x_Symbol] :=
  a*Int[1/((e+f*x)*Sqrt[1-(c+d*x)^2]),x] + 
  b*Int[ArcCos[c+d*x]/((e+f*x)*Sqrt[1-(c+d*x)^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f]


Int[(a_.+b_.*ArcSin[c_.+d_.*x_])^n_./((e_.+f_.*x_)^2*Sqrt[u_]),x_Symbol] :=
  -Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])^n/(f*(e+f*x)) + 
  b*n*d/f*Int[(a+b*ArcSin[c+d*x])^(n-1)/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCos[c_.+d_.*x_])^n_./((e_.+f_.*x_)^2*Sqrt[u_]),x_Symbol] :=
  -Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])^n/(f*(e+f*x)) - 
  b*n*d/f*Int[(a+b*ArcCos[c+d*x])^(n-1)/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[n] && n>0


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  (e+f*x)^(m+1)*Sqrt[1-(c+d*x)^2]*(a+b*ArcSin[c+d*x])^n/(f*(m+1)) - 
  b*n*d/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcSin[c+d*x])^(n-1),x] + 
  d^2*(m+2)/(f^2*(m+1))*Int[(e+f*x)^(m+2)*(a+b*ArcSin[c+d*x])^n/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  (e+f*x)^(m+1)*Sqrt[1-(c+d*x)^2]*(a+b*ArcCos[c+d*x])^n/(f*(m+1)) + 
  b*n*d/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcCos[c+d*x])^(n-1),x] + 
  d^2*(m+2)/(f^2*(m+1))*Int[(e+f*x)^(m+2)*(a+b*ArcCos[c+d*x])^n/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcSin[c_.+d_.*x_])/Sqrt[u_],x_Symbol] :=
  (e+f*x)^m*(c+d*x)*(a+b*ArcSin[c+d*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,(c+d*x)^2]/(d*(m+1)) - 
  b*(e+f*x)^m*(c+d*x)^2*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},(c+d*x)^2]/(d*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && Not[NegativeIntegerQ[m]]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCos[c_.+d_.*x_])/Sqrt[u_],x_Symbol] :=
  (e+f*x)^m*(c+d*x)*(a+b*ArcCos[c+d*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,(c+d*x)^2]/(d*(m+1)) + 
  b*(e+f*x)^m*(c+d*x)^2*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},(c+d*x)^2]/(d*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && ZeroQ[d*e-c*f] && Not[NegativeIntegerQ[m]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_/Sqrt[u_],x_Symbol] :=
  (e+f*x)^m*(a+b*ArcSin[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*ArcSin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && RationalQ[m,n] && m>0 && n<-1


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_/Sqrt[u_],x_Symbol] :=
  -(e+f*x)^m*(a+b*ArcCos[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*ArcCos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && RationalQ[m,n] && m>0 && n<-1


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_/Sqrt[u_],x_Symbol] :=
  2/(b*d^(m+1))*Subst[Int[x^(2*n+1)*(d*e-c*f+f*Sin[x^2/b-a/b])^m,x],x,Sqrt[a+b*ArcSin[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && IntegerQ[m] && IntegerQ[n-1/2]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_/Sqrt[u_],x_Symbol] :=
  -2/(b*d^(m+1))*Subst[Int[x^(2*n+1)*(d*e-c*f+f*Cos[x^2/b-a/b])^m,x],x,Sqrt[a+b*ArcCos[c+d*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[u-(1-(c+d*x)^2)] && IntegerQ[m] && IntegerQ[n-1/2]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  1/(b*d^(m+1))*Subst[Int[x^n*(d*e-c*f+f*Sin[x/b-a/b])^m,x],x,a+b*ArcSin[c+d*x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[u-(1-(c+d*x)^2)] && IntegerQ[m] && Not[IntegerQ[n-1/2]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  -1/(b*d^(m+1))*Subst[Int[x^n*(d*e-c*f+f*Cos[x/b-a/b])^m,x],x,a+b*ArcCos[c+d*x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[u-(1-(c+d*x)^2)] && IntegerQ[m] && Not[IntegerQ[n-1/2]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcSin[c+d*x])^n/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[u-(1-(c+d*x)^2)]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_])^n_./Sqrt[u_],x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcCos[c+d*x])^n/Sqrt[1-(c+d*x)^2],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[u-(1-(c+d*x)^2)]


Int[x_^q_.*(a_.+b_.*ArcSin[c_.+d_.*x_^p_])^n_.,x_Symbol] :=
  1/p*Subst[Int[(a+b*ArcSin[c+d*x])^n,x],x,x^p] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[q-(p-1)]


Int[x_^q_.*(a_.+b_.*ArcCos[c_.+d_.*x_^p_])^n_.,x_Symbol] :=
  1/p*Subst[Int[(a+b*ArcCos[c+d*x])^n,x],x,x^p] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[q-(p-1)]


Int[x_^q_.*(e_.+f_.*x_^p_)^m_.*(a_.+b_.*ArcSin[c_.+d_.*x_^p_])^n_.,x_Symbol] :=
  1/p*Subst[Int[(e+f*x)^m*(a+b*ArcSin[c+d*x])^n,x],x,x^p] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[q-(p-1)]


Int[x_^q_.*(e_.+f_.*x_^p_)^m_.*(a_.+b_.*ArcCos[c_.+d_.*x_^p_])^n_.,x_Symbol] :=
  1/p*Subst[Int[(e+f*x)^m*(a+b*ArcCos[c+d*x])^n,x],x,x^p] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[q-(p-1)]


Int[ArcSin[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Cot[x],x],x,ArcSin[a*x^p]] /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0


Int[ArcCos[a_.*x_^p_]^n_./x_,x_Symbol] :=
  -1/p*Subst[Int[x^n*Tan[x],x],x,ArcCos[a*x^p]] /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0


Int[u_.*ArcSin[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCsc[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCos[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSec[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_^m_.*ArcSin[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[x^n*Cos[x]^(2*m+1),x],x,ArcSin[a+b*x]] /;
FreeQ[{a,b,n},x] && ZeroQ[u-(1-(a+b*x)^2)] && IntegerQ[2*m]


Int[u_^m_.*ArcCos[a_.+b_.*x_]^n_.,x_Symbol] :=
  -1/b*Subst[Int[x^n*Sin[x]^(2*m+1),x],x,ArcCos[a+b*x]] /;
FreeQ[{a,b,n},x] && ZeroQ[u-(1-(a+b*x)^2)] && IntegerQ[2*m]


Int[u_.*f_^(c_.*ArcSin[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[ReplaceAll[u,x->-a/b+Sin[x]/b]*f^(c*x^n)*Cos[x],x],x,ArcSin[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[u_.*f_^(c_.*ArcCos[a_.+b_.*x_]^n_.),x_Symbol] :=
  -1/b*Subst[Int[ReplaceAll[u,x->-a/b+Cos[x]/b]*f^(c*x^n)*Sin[x],x],x,ArcCos[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[(c_.+d_.*x_^2)^n_*ArcSin[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcSin[a*x],u,x] - 
  a*Int[Dist[1/Sqrt[1-a^2*x^2],u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[n+1/2] && n<=-1


Int[(c_.+d_.*x_^2)^n_*ArcCos[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcCos[a*x],u,x] + 
  a*Int[Dist[1/Sqrt[1-a^2*x^2],u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[n+1/2] && n<=-1


Int[x_^m_.*(c_.+d_.*x_^2)^n_*ArcSin[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(c+d*x^2)^n,x]]},  
  Dist[ArcSin[a*x],u,x] - 
  a*Int[Dist[1/Sqrt[1-a^2*x^2],u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[n+1/2] && ZeroQ[a^2*c+d] && (EvenQ[m] || PositiveIntegerQ[m]) 


Int[x_^m_.*(c_.+d_.*x_^2)^n_*ArcCos[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(c+d*x^2)^n,x]]},  
  Dist[ArcCos[a*x],u,x] + 
  a*Int[Dist[1/Sqrt[1-a^2*x^2],u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[n+1/2] && ZeroQ[a^2*c+d] && (EvenQ[m] || PositiveIntegerQ[m]) 


Int[ArcSin[u_],x_Symbol] :=
  x*ArcSin[u] -
  Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1-u^2],x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCos[u_],x_Symbol] :=
  x*ArcCos[u] +
  Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1-u^2],x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[x_^m_.*ArcSin[u_],x_Symbol] :=
  x^(m+1)*ArcSin[u]/(m+1) -
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	Not[FunctionOfExponentialQ[u,x]]


Int[x_^m_.*ArcCos[u_],x_Symbol] :=
  x^(m+1)*ArcCos[u]/(m+1) +
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	Not[FunctionOfExponentialQ[u,x]]


Int[v_*ArcSin[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[ArcSin[u],w,x] -
  Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x]


Int[v_*ArcCos[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[ArcCos[u],w,x] +
  Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x]


Int[ArcTan[a_.*x_]^n_.,x_Symbol] :=
  x*ArcTan[a*x]^n -
  a*n*Int[x*ArcTan[a*x]^(n-1)/(1+a^2*x^2),x] /;
FreeQ[a,x] && PositiveIntegerQ[n]


Int[ArcCot[a_.*x_]^n_.,x_Symbol] :=
  x*ArcCot[a*x]^n +
  a*n*Int[x*ArcCot[a*x]^(n-1)/(1+a^2*x^2),x] /;
FreeQ[a,x] && PositiveIntegerQ[n]


Int[ArcTan[a_.*x_]^n_,x_Symbol] :=
  Defer[Int][ArcTan[a*x]^n,x] /;
FreeQ[{a,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcCot[a_.*x_]^n_,x_Symbol] :=
  Defer[Int][ArcCot[a*x]^n,x] /;
FreeQ[{a,n},x] && Not[PositiveIntegerQ[n]]


Int[x_*ArcTan[a_.*x_],x_Symbol] :=
  -x/(2*a) + x^2*ArcTan[a*x]/2 + ArcTan[a*x]/(2*a^2) /;
FreeQ[a,x]


Int[x_*ArcCot[a_.*x_],x_Symbol] :=
  x/(2*a) + x^2*ArcCot[a*x]/2 + ArcCot[a*x]/(2*a^2) /;
FreeQ[a,x]


Int[x_^m_*ArcTan[a_.*x_],x_Symbol] :=
  -x^m/(a*m*(m+1)) + 
  x^(m+1)*ArcTan[a*x]/(m+1) + 
  x^(m-1)*ArcTan[a*x]/(a^2*(m+1)) - 
  (m-1)/(a^2*(m+1))*Int[x^(m-2)*ArcTan[a*x],x] /;
FreeQ[a,x] && RationalQ[m] && m>1


Int[x_^m_*ArcCot[a_.*x_],x_Symbol] :=
  x^m/(a*m*(m+1)) + 
  x^(m+1)*ArcCot[a*x]/(m+1) + 
  x^(m-1)*ArcCot[a*x]/(a^2*(m+1)) - 
  (m-1)/(a^2*(m+1))*Int[x^(m-2)*ArcCot[a*x],x] /;
FreeQ[a,x] && RationalQ[m] && m>1


Int[ArcTan[a_.*x_]/x_,x_Symbol] :=
  I/2*Int[Log[1-I*a*x]/x, x] - 
  I/2*Int[Log[1+I*a*x]/x, x] /;
FreeQ[a,x]


Int[ArcCot[a_.*x_]/x_,x_Symbol] :=
  I/2*Int[Log[1-I/(a*x)]/x,x] - 
  I/2*Int[Log[1+I/(a*x)]/x,x] /;
FreeQ[a,x]


Int[ArcTan[a_.*x_]/x_^2,x_Symbol] :=
  -ArcTan[a*x]/x - a*ArcTanh[1+2*a^2*x^2] /;
FreeQ[a,x]


Int[ArcCot[a_.*x_]/x_^2,x_Symbol] :=
  -ArcCot[a*x]/x + a*ArcCoth[1+2*a^2*x^2] /;
FreeQ[a,x]


Int[ArcTan[a_.*x_]/x_^3,x_Symbol] :=
  -a/(2*x) - ArcTan[a*x]/(2*x^2) - a^2*ArcTan[a*x]/2 /;
FreeQ[a,x]


Int[ArcCot[a_.*x_]/x_^3,x_Symbol] :=
  a/(2*x) - ArcCot[a*x]/(2*x^2) - a^2*ArcCot[a*x]/2 /;
FreeQ[a,x]


Int[x_^m_*ArcTan[a_.*x_],x_Symbol] :=
  -a*x^(m+2)/((m+1)*(m+2)) + 
  x^(m+1)*ArcTan[a*x]/(m+1) + 
  a^2*x^(m+3)*ArcTan[a*x]/(m+1) - 
  a^2*(m+3)/(m+1)*Int[x^(m+2)*ArcTan[a*x],x] /;
FreeQ[a,x] && RationalQ[m] && m<-3


Int[x_^m_*ArcCot[a_.*x_],x_Symbol] :=
  a*x^(m+2)/((m+1)*(m+2)) + 
  x^(m+1)*ArcCot[a*x]/(m+1) + 
  a^2*x^(m+3)*ArcCot[a*x]/(m+1) - 
  a^2*(m+3)/(m+1)*Int[x^(m+2)*ArcCot[a*x],x] /;
FreeQ[a,x] && RationalQ[m] && m<-3


Int[ArcTan[a_.*x_]^n_/x_,x_Symbol] :=
  2*ArcTan[a*x]^n*ArcTanh[1-2*I/(I-a*x)] -
  2*a*n*Int[ArcTan[a*x]^(n-1)*ArcTanh[1-2*I/(I-a*x)]/(1+a^2*x^2),x] /;
FreeQ[a,x] && IntegerQ[n] && n>1


Int[ArcCot[a_.*x_]^n_/x_,x_Symbol] :=
  2*ArcCot[a*x]^n*ArcCoth[1-2*I/(I-a*x)] +
  2*a*n*Int[ArcCot[a*x]^(n-1)*ArcCoth[1-2*I/(I-a*x)]/(1+a^2*x^2),x] /;
FreeQ[a,x] && IntegerQ[n] && n>1


Int[x_^m_.*ArcTan[a_.*x_]^n_,x_Symbol] :=
  x^(m+1)*ArcTan[a*x]^n/(m+1) - 
  a*n/(m+1)*Int[x^(m+1)*ArcTan[a*x]^(n-1)/(1+a^2*x^2),x] /;
FreeQ[{a,m},x] && IntegerQ[n] && n>1 && NonzeroQ[m+1]


Int[x_^m_.*ArcCot[a_.*x_]^n_,x_Symbol] :=
  x^(m+1)*ArcCot[a*x]^n/(m+1) + 
  a*n/(m+1)*Int[x^(m+1)*ArcCot[a*x]^(n-1)/(1+a^2*x^2),x] /;
FreeQ[{a,m},x] && IntegerQ[n] && n>1 && NonzeroQ[m+1]


Int[x_^m_.*ArcTan[a_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcTan[a*x]^n,x] /;
FreeQ[{a,m,n},x] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*ArcCot[a_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcCot[a*x]^n,x] /;
FreeQ[{a,m,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcTan[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  -ArcTan[a*x]^n*Log[2*c/(c+d*x)]/d +
  a*n/d*Int[ArcTan[a*x]^(n-1)*Log[2*c/(c+d*x)]/(1+a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n]


Int[ArcCot[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  -ArcCot[a*x]^n*Log[2*c/(c+d*x)]/d -
  a*n/d*Int[ArcCot[a*x]^(n-1)*Log[2*c/(c+d*x)]/(1+a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n]


Int[ArcTan[a_.*x_]^n_/(c_+d_.*x_),x_Symbol] :=
  Defer[Int][ArcTan[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c^2+d^2] && Not[PositiveIntegerQ[n]]


Int[ArcCot[a_.*x_]^n_/(c_+d_.*x_),x_Symbol] :=
  Defer[Int][ArcCot[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c^2+d^2] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*ArcTan[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  1/d*Int[x^(m-1)*ArcTan[a*x]^n,x] -
  c/d*Int[x^(m-1)*ArcTan[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  1/d*Int[x^(m-1)*ArcCot[a*x]^n,x] -
  c/d*Int[x^(m-1)*ArcCot[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[ArcTan[a_.*x_]^n_./(x_*(c_+d_.*x_)),x_Symbol] :=
  ArcTan[a*x]^n*Log[2*d*x/(c+d*x)]/c - 
  a*n/c*Int[ArcTan[a*x]^(n-1)*Log[2*d*x/(c+d*x)]/(1+a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n]


Int[ArcTan[a_.*x_]^n_./(c_.*x_+d_.*x_^2),x_Symbol] :=
  ArcTan[a*x]^n*Log[2*d*x/(c+d*x)]/c - 
  a*n/c*Int[ArcTan[a*x]^(n-1)*Log[2*d*x/(c+d*x)]/(1+a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n]


Int[ArcCot[a_.*x_]^n_./(x_*(c_+d_.*x_)),x_Symbol] :=
  ArcCot[a*x]^n*Log[2*d*x/(c+d*x)]/c +
  a*n/c*Int[ArcCot[a*x]^(n-1)*Log[2*d*x/(c+d*x)]/(1+a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n]


Int[ArcCot[a_.*x_]^n_./(c_.*x_+d_.*x_^2),x_Symbol] :=
  ArcCot[a*x]^n*Log[2*d*x/(c+d*x)]/c +
  a*n/c*Int[ArcCot[a*x]^(n-1)*Log[2*d*x/(c+d*x)]/(1+a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n]


Int[x_^m_*ArcTan[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  1/c*Int[x^m*ArcTan[a*x]^n,x] -
  d/c*Int[x^(m+1)*ArcTan[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_*ArcCot[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
  1/c*Int[x^m*ArcCot[a*x]^n,x] -
  d/c*Int[x^(m+1)*ArcCot[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_.*ArcTan[a_.*x_]^n_/(c_+d_.*x_),x_Symbol] :=
  Defer[Int][x^m*ArcTan[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d,m,n},x] && ZeroQ[a^2*c^2+d^2] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*ArcCot[a_.*x_]^n_/(c_+d_.*x_),x_Symbol] :=
  Defer[Int][x^m*ArcCot[a*x]^n/(c+d*x),x] /;
FreeQ[{a,c,d,m,n},x] && ZeroQ[a^2*c^2+d^2] && Not[PositiveIntegerQ[n]]


Int[(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_],x_Symbol] :=
  -(c+d*x^2)^p/(2*a*p*(2*p+1)) + 
  x*(c+d*x^2)^p*ArcTan[a*x]/(2*p+1) + 
  2*c*p/(2*p+1)*Int[(c+d*x^2)^(p-1)*ArcTan[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p>0


Int[(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_],x_Symbol] :=
  (c+d*x^2)^p/(2*a*p*(2*p+1)) + 
  x*(c+d*x^2)^p*ArcCot[a*x]/(2*p+1) + 
  2*c*p/(2*p+1)*Int[(c+d*x^2)^(p-1)*ArcCot[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p>0


Int[(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_,x_Symbol] :=
  -n*(c+d*x^2)^p*ArcTan[a*x]^(n-1)/(2*a*p*(2*p+1)) + 
  x*(c+d*x^2)^p*ArcTan[a*x]^n/(2*p+1) + 
  2*c*p/(2*p+1)*Int[(c+d*x^2)^(p-1)*ArcTan[a*x]^n,x] + 
  c*n*(n-1)/(2*p*(2*p+1))*Int[(c+d*x^2)^(p-1)*ArcTan[a*x]^(n-2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n,p] && p>0 && n>1


Int[(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_,x_Symbol] :=
  n*(c+d*x^2)^p*ArcCot[a*x]^(n-1)/(2*a*p*(2*p+1)) + 
  x*(c+d*x^2)^p*ArcCot[a*x]^n/(2*p+1) + 
  2*c*p/(2*p+1)*Int[(c+d*x^2)^(p-1)*ArcCot[a*x]^n,x] + 
  c*n*(n-1)/(2*p*(2*p+1))*Int[(c+d*x^2)^(p-1)*ArcCot[a*x]^(n-2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n,p] && p>0 && n>1


Int[1/((c_+d_.*x_^2)*ArcTan[a_.*x_]),x_Symbol] :=
  Log[ArcTan[a*x]]/(a*c) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]


Int[1/((c_+d_.*x_^2)*ArcCot[a_.*x_]),x_Symbol] :=
  -Log[ArcCot[a*x]]/(a*c) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]


Int[ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  ArcTan[a*x]^(n+1)/(a*c*(n+1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n+1]


Int[ArcCot[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  -ArcCot[a*x]^(n+1)/(a*c*(n+1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n+1]


Int[ArcTan[a_.*x_]/Sqrt[u_],x_Symbol] :=
  -2*I*ArcTan[a*x]*ArcTan[Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/a + 
  I*PolyLog[2,-I*Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/a -
  I*PolyLog[2,I*Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/a /;
FreeQ[a,x] && ZeroQ[u-(1+a^2*x^2)]


Int[ArcCot[a_.*x_]/Sqrt[u_],x_Symbol] :=
  -2*I*ArcCot[a*x]*ArcTan[Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/a -
  I*PolyLog[2,-I*Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/a +
  I*PolyLog[2,I*Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/a /;
FreeQ[a,x] && ZeroQ[u-(1+a^2*x^2)]


Int[ArcTan[a_.*x_]^n_./Sqrt[u_],x_Symbol] :=
  1/a*Subst[Int[x^n*Sec[x],x],x,ArcTan[a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1+a^2*x^2)] && IntegerQ[n] && n>1


Int[ArcCot[a_.*x_]^n_./Sqrt[u_],x_Symbol] :=
  -x*Sqrt[1+1/(a^2*x^2)]/Sqrt[1+a^2*x^2]*Subst[Int[x^n*Csc[x],x],x,ArcCot[a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1+a^2*x^2)] && IntegerQ[n] && n>1


Int[ArcTan[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcTan[a*x]^n/Sqrt[1+a^2*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n] && NonzeroQ[c-1]


Int[ArcCot[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcCot[a*x]^n/Sqrt[1+a^2*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n] && NonzeroQ[c-1]


Int[ArcTan[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Defer[Int][ArcTan[a*x]^n/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[PositiveIntegerQ[n]]


Int[ArcCot[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Defer[Int][ArcCot[a*x]^n/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[PositiveIntegerQ[n]]


Int[ArcTan[a_.*x_]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  1/(a*c*Sqrt[c+d*x^2]) +
  x*ArcTan[a*x]/(c*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]


Int[ArcCot[a_.*x_]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -1/(a*c*Sqrt[c+d*x^2]) +
  x*ArcCot[a*x]/(c*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]


Int[ArcTan[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  n*ArcTan[a*x]^(n-1)/(a*c*Sqrt[c+d*x^2]) +
  x*ArcTan[a*x]^n/(c*Sqrt[c+d*x^2]) -
  n*(n-1)*Int[ArcTan[a*x]^(n-2)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>1


Int[ArcCot[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -n*ArcCot[a*x]^(n-1)/(a*c*Sqrt[c+d*x^2]) +
  x*ArcCot[a*x]^n/(c*Sqrt[c+d*x^2]) -
  n*(n-1)*Int[ArcCot[a*x]^(n-2)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>1


Int[1/((c_+d_.*x_^2)^(3/2)*ArcTan[a_.*x_]),x_Symbol] :=
  1/(a*c^(3/2))*Subst[Int[Cos[x]/x,x],x,ArcTan[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveQ[c]


Int[1/((c_+d_.*x_^2)^(3/2)*ArcTan[a_.*x_]),x_Symbol] :=
  Sqrt[c+d*x^2]/(c^2*Sqrt[1+a^2*x^2])*Int[1/((1+a^2*x^2)^(3/2)*ArcTan[a*x]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]]


Int[1/((c_+d_.*x_^2)^(3/2)*ArcCot[a_.*x_]),x_Symbol] :=
  -x*Sqrt[(1+a^2*x^2)/(a^2*x^2)]/(c*Sqrt[c+d*x^2])*Subst[Int[Sin[x]/x,x],x,ArcCot[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]


Int[1/((c_+d_.*x_^2)^(3/2)*ArcTan[a_.*x_]^2),x_Symbol] :=
  -1/(a*c*Sqrt[c+d*x^2]*ArcTan[a*x]) - 
  a*Int[x/((c+d*x^2)^(3/2)*ArcTan[a*x]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]


Int[1/((c_+d_.*x_^2)^(3/2)*ArcCot[a_.*x_]^2),x_Symbol] :=
  1/(a*c*Sqrt[c+d*x^2]*ArcCot[a*x]) + 
  a*Int[x/((c+d*x^2)^(3/2)*ArcCot[a*x]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]


Int[ArcTan[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  ArcTan[a*x]^(n+1)/(a*c*(n+1)*Sqrt[c+d*x^2]) +
  x*ArcTan[a*x]^(n+2)/(c*(n+1)*(n+2)*Sqrt[c+d*x^2]) -
  1/((n+1)*(n+2))*Int[ArcTan[a*x]^(n+2)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n<-1 && n!=-2


Int[ArcCot[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -ArcCot[a*x]^(n+1)/(a*c*(n+1)*Sqrt[c+d*x^2]) +
  x*ArcCot[a*x]^(n+2)/(c*(n+1)*(n+2)*Sqrt[c+d*x^2]) -
  1/((n+1)*(n+2))*Int[ArcCot[a*x]^(n+2)/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n<-1 && n!=-2


Int[(c_+d_.*x_^2)^p_*ArcTan[a_.*x_],x_Symbol] :=
  (c+d*x^2)^(p+1)/(4*a*c*(p+1)^2) -
  x*(c+d*x^2)^(p+1)*ArcTan[a*x]/(2*c*(p+1)) +
  (2*p+3)/(2*c*(p+1))*Int[(c+d*x^2)^(p+1)*ArcTan[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<-1 && p!=-3/2


Int[(c_+d_.*x_^2)^p_*ArcCot[a_.*x_],x_Symbol] :=
  -(c+d*x^2)^(p+1)/(4*a*c*(p+1)^2) -
  x*(c+d*x^2)^(p+1)*ArcCot[a*x]/(2*c*(p+1)) +
  (2*p+3)/(2*c*(p+1))*Int[(c+d*x^2)^(p+1)*ArcCot[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<-1 && p!=-3/2


Int[(c_+d_.*x_^2)^p_*Sqrt[ArcTan[a_.*x_]],x_Symbol] :=
  2*c^p/a*Subst[Int[x^2*Sec[x^2]^(2*(p+1)),x],x,Sqrt[ArcTan[a*x]]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[p] && p<-1


Int[(c_+d_.*x_^2)^p_*Sqrt[ArcCot[a_.*x_]],x_Symbol] :=
  -2*c^p/a*Subst[Int[x^2*Csc[x^2]^(2*(p+1)),x],x,Sqrt[ArcCot[a*x]]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[p] && p<-1


Int[(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_,x_Symbol] :=
  n*(c+d*x^2)^(p+1)*ArcTan[a*x]^(n-1)/(4*a*c*(p+1)^2) -
  x*(c+d*x^2)^(p+1)*ArcTan[a*x]^n/(2*c*(p+1)) +
  (2*p+3)/(2*c*(p+1))*Int[(c+d*x^2)^(p+1)*ArcTan[a*x]^n,x] -
  n*(n-1)/(4*(p+1)^2)*Int[(c+d*x^2)^p*ArcTan[a*x]^(n-2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n,p] && p<-1 && p!=-3/2 && n>1


Int[(c_+d_.*x_^2)^p_*ArcCot[a_.*x_]^n_,x_Symbol] :=
  -n*(c+d*x^2)^(p+1)*ArcCot[a*x]^(n-1)/(4*a*c*(p+1)^2) -
  x*(c+d*x^2)^(p+1)*ArcCot[a*x]^n/(2*c*(p+1)) +
  (2*p+3)/(2*c*(p+1))*Int[(c+d*x^2)^(p+1)*ArcCot[a*x]^n,x] -
  n*(n-1)/(4*(p+1)^2)*Int[(c+d*x^2)^p*ArcCot[a*x]^(n-2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n,p] && p<-1 && p!=-3/2 && n>1


Int[(c_+d_.*x_^2)^p_/ArcTan[a_.*x_],x_Symbol] :=
  c^p/a*Subst[Int[Expand[TrigReduce[Sec[x]^(2*(p+1))/x]],x],x,ArcTan[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[2*p] && p<-1 && (IntegerQ[p] || PositiveQ[c])


Int[(c_+d_.*x_^2)^p_/ArcCot[a_.*x_],x_Symbol] :=
  -c^p/a*Subst[Int[Expand[TrigReduce[Csc[x]^(2*(p+1))/x]],x],x,ArcCot[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[p] && p<-1


Int[(c_+d_.*x_^2)^p_/ArcTan[a_.*x_],x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[(1+a^2*x^2)^p/ArcTan[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[p+1/2] && p<-1 && Not[PositiveQ[c]]


Int[(c_+d_.*x_^2)^p_/ArcCot[a_.*x_],x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[(1+a^2*x^2)^p/ArcCot[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[p+1/2] && p<-1 && Not[PositiveQ[c]]


Int[(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcTan[a*x]^(n+1)/(a*c*(n+1)) -
  2*a*(p+1)/(n+1)*Int[x*(c+d*x^2)^p*ArcTan[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n,p] && p<-1 && p!=-3/2 && n<-1


Int[(c_+d_.*x_^2)^p_*ArcCot[a_.*x_]^n_,x_Symbol] :=
  -(c+d*x^2)^(p+1)*ArcCot[a*x]^(n+1)/(a*c*(n+1)) +
  2*a*(p+1)/(n+1)*Int[x*(c+d*x^2)^p*ArcCot[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n,p] && p<-1 && p!=-3/2 && n<-1


Int[(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  Defer[Int][(c+d*x^2)^p*ArcTan[a*x]^n,x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c]


Int[(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  Defer[Int][(c+d*x^2)^p*ArcCot[a*x]^n,x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c]


Int[x_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcTan[a*x]^n/(2*d*(p+1)) - 
  n/(2*a*(p+1))*Int[(c+d*x^2)^p*ArcTan[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p>0 && PositiveIntegerQ[n]


Int[x_*(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcCot[a*x]^n/(2*d*(p+1)) +
  n/(2*a*(p+1))*Int[(c+d*x^2)^p*ArcCot[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p>0 && PositiveIntegerQ[n]


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  x^(m+1)*(c+d*x^2)^(p+1)*ArcTan[a*x]^n/(c*(m+1)) -
  a*n/(m+1)*Int[x^(m+1)*(c+d*x^2)^p*ArcTan[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,p] && p>0 && PositiveIntegerQ[n] && ZeroQ[m+2*p+3]


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  x^(m+1)*(c+d*x^2)^(p+1)*ArcCot[a*x]^n/(c*(m+1)) +
  a*n/(m+1)*Int[x^(m+1)*(c+d*x^2)^p*ArcCot[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,p] && p>0 && PositiveIntegerQ[n] && ZeroQ[m+2*p+3]


Int[x_^m_.*Sqrt[c_+d_.*x_^2]*ArcTan[a_.*x_],x_Symbol] :=
  x^(m+1)*Sqrt[c+d*x^2]*ArcTan[a*x]/(m+2) - 
  a*c/(m+2)*Int[x^(m+1)/Sqrt[c+d*x^2],x] + 
  c/(m+2)*Int[x^m*ArcTan[a*x]/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && NonzeroQ[m+2]


Int[x_^m_.*Sqrt[c_+d_.*x_^2]*ArcCot[a_.*x_],x_Symbol] :=
  x^(m+1)*Sqrt[c+d*x^2]*ArcCot[a*x]/(m+2) + 
  a*c/(m+2)*Int[x^(m+1)/Sqrt[c+d*x^2],x] + 
  c/(m+2)*Int[x^m*ArcCot[a*x]/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && NonzeroQ[m+2]


Int[x_^m_.*(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(c+d*x^2)^p*ArcTan[a*x]^n,x],x] /;
FreeQ[{a,c,d,m},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_.*(c_+d_.*x_^2)^p_*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(c+d*x^2)^p*ArcCot[a*x]^n,x],x] /;
FreeQ[{a,c,d,m},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  c*Int[x^m*(c+d*x^2)^(p-1)*ArcTan[a*x]^n,x] + 
  a^2*c*Int[x^(m+2)*(c+d*x^2)^(p-1)*ArcTan[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,p] && p>0 && PositiveIntegerQ[n] && NonzeroQ[m+2*p+3]


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  c*Int[x^m*(c+d*x^2)^(p-1)*ArcCot[a*x]^n,x] + 
  a^2*c*Int[x^(m+2)*(c+d*x^2)^(p-1)*ArcCot[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,p] && p>0 && PositiveIntegerQ[n] && NonzeroQ[m+2*p+3]


Int[x_*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  -I*ArcTan[a*x]^(n+1)/(d*(n+1)) - 
  1/(a*c)*Int[ArcTan[a*x]^n/(I-a*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[x_*ArcCot[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  I*ArcCot[a*x]^(n+1)/(d*(n+1)) - 
  1/(a*c)*Int[ArcCot[a*x]^n/(I-a*x),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[x_^m_*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/d*Int[x^(m-2)*ArcTan[a*x]^n,x] -
  c/d*Int[x^(m-2)*ArcTan[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*ArcCot[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/d*Int[x^(m-2)*ArcCot[a*x]^n,x] -
  c/d*Int[x^(m-2)*ArcCot[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n] && n>0 && m>1


Int[ArcTan[a_.*x_]^n_./(x_*(c_+d_.*x_^2)),x_Symbol] :=
  -I*ArcTan[a*x]^(n+1)/(c*(n+1)) +
  I/c*Int[ArcTan[a*x]^n/(x*(I+a*x)),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[ArcTan[a_.*x_]^n_./(c_.*x_+d_.*x_^3),x_Symbol] :=
  -I*ArcTan[a*x]^(n+1)/(c*(n+1)) +
  I/c*Int[ArcTan[a*x]^n/(x*(I+a*x)),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[ArcCot[a_.*x_]^n_./(x_*(c_+d_.*x_^2)),x_Symbol] :=
  I*ArcCot[a*x]^(n+1)/(c*(n+1)) +
  I/c*Int[ArcCot[a*x]^n/(x*(I+a*x)),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[ArcCot[a_.*x_]^n_./(c_.*x_+d_.*x_^3),x_Symbol] :=
  I*ArcCot[a*x]^(n+1)/(c*(n+1)) +
  I/c*Int[ArcCot[a*x]^n/(x*(I+a*x)),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[x_^m_*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/c*Int[x^m*ArcTan[a*x]^n,x] -
  d/c*Int[x^(m+2)*ArcTan[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*ArcCot[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/c*Int[x^m*ArcCot[a*x]^n,x] -
  d/c*Int[x^(m+2)*ArcCot[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_.*ArcTan[a_.*x_]^n_/(c_+d_.*x_^2),x_Symbol] :=
  x^m*ArcTan[a*x]^(n+1)/(a*c*(n+1)) - 
  m/(a*c*(n+1))*Int[x^(m-1)*ArcTan[a*x]^(n+1),x] /;
FreeQ[{a,c,d,m},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n<-1


Int[x_^m_.*ArcCot[a_.*x_]^n_/(c_+d_.*x_^2),x_Symbol] :=
  -x^m*ArcCot[a*x]^(n+1)/(a*c*(n+1)) + 
  m/(a*c*(n+1))*Int[x^(m-1)*ArcCot[a*x]^(n+1),x] /;
FreeQ[{a,c,d,m},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n<-1


Int[x_*ArcTan[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[c+d*x^2]*ArcTan[a*x]^n/d - 
  n/a*Int[ArcTan[a*x]^(n-1)/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[x_*ArcCot[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[c+d*x^2]*ArcCot[a*x]^n/d + 
  n/a*Int[ArcCot[a*x]^(n-1)/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[x_^m_.*ArcTan[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null},Int[x^m/Sqrt[c+d*x^2],x]]},
  Dist[ArcTan[a*x]^n,u,x] - 
  a*c*n*Int[Dist[ArcTan[a*x]^(n-1)/(c+d*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n,(m+1)/2]


Int[x_^m_.*ArcCot[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null},Int[x^m/Sqrt[c+d*x^2],x]]},
  Dist[ArcCot[a*x]^n,u,x] + 
  a*c*n*Int[Dist[ArcCot[a*x]^(n-1)/(c+d*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n,(m+1)/2]


Int[x_^m_.*ArcTan[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null},Int[(Binomial[m-1,m/2]-2^(m-1)*a^m*x^m)/Sqrt[c+d*x^2],x]]},
  Binomial[m-1,m/2]/(2^(m-1)*a^m)*Int[ArcTan[a*x]^n/Sqrt[c+d*x^2],x] -
  Dist[ArcTan[a*x]^n/(2^(m-1)*a^m),u,x] + 
  a*c*n/(2^(m-1)*a^m)*Int[Dist[ArcTan[a*x]^(n-1)/(c+d*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n,m/2]


Int[x_^m_.*ArcCot[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null},Int[(Binomial[m-1,m/2]-2^(m-1)*a^m*x^m)/Sqrt[c+d*x^2],x]]},
  Binomial[m-1,m/2]/(2^(m-1)*a^m)*Int[ArcCot[a*x]^n/Sqrt[c+d*x^2],x] -
  Dist[ArcCot[a*x]^n/(2^(m-1)*a^m),u,x] - 
  a*c*n/(2^(m-1)*a^m)*Int[Dist[ArcCot[a*x]^(n-1)/(c+d*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n,m/2]


Int[ArcTan[a_.*x_]/(x_*Sqrt[u_]),x_Symbol] :=
  -2*ArcTan[a*x]*ArcTanh[Sqrt[1+I*a*x]/Sqrt[1-I*a*x]] + 
  I*PolyLog[2,-Sqrt[1+I*a*x]/Sqrt[1-I*a*x]] - 
  I*PolyLog[2,Sqrt[1+I*a*x]/Sqrt[1-I*a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1+a^2*x^2)]


Int[ArcCot[a_.*x_]/(x_*Sqrt[u_]),x_Symbol] :=
  -2*ArcCot[a*x]*ArcTanh[Sqrt[1+I*a*x]/Sqrt[1-I*a*x]] - 
  I*PolyLog[2,-Sqrt[1+I*a*x]/Sqrt[1-I*a*x]] + 
  I*PolyLog[2,Sqrt[1+I*a*x]/Sqrt[1-I*a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1+a^2*x^2)]


Int[ArcTan[a_.*x_]^n_/(x_*Sqrt[u_]),x_Symbol] :=
  Subst[Int[x^n*Csc[x],x],x,ArcTan[a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1+a^2*x^2)] && IntegerQ[n] && n>1


Int[ArcCot[a_.*x_]^n_/(x_*Sqrt[u_]),x_Symbol] :=
  -a*x*Sqrt[1+1/(a^2*x^2)]/Sqrt[1+a^2*x^2]*Subst[Int[x^n*Sec[x],x],x,ArcCot[a*x]] /;
FreeQ[a,x] && ZeroQ[u-(1+a^2*x^2)] && IntegerQ[n] && n>1


Int[ArcTan[a_.*x_]^n_./(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcTan[a*x]^n/(x*Sqrt[1+a^2*x^2]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n] && NonzeroQ[c-1]


Int[ArcCot[a_.*x_]^n_./(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcCot[a*x]^n/(x*Sqrt[1+a^2*x^2]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveIntegerQ[n] && NonzeroQ[c-1]


Int[ArcTan[a_.*x_]^n_./(x_^2*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  -Sqrt[c+d*x^2]*ArcTan[a*x]^n/(c*x) + 
  a*n*Int[ArcTan[a*x]^(n-1)/(x*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[ArcCot[a_.*x_]^n_./(x_^2*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  -Sqrt[c+d*x^2]*ArcCot[a*x]^n/(c*x) - 
  a*n*Int[ArcCot[a*x]^(n-1)/(x*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0


Int[x_^m_*ArcTan[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[c+d*x^2]*ArcTan[a*x]^n/(c*(m+1)) - 
  a*n/(m+1)*Int[x^(m+1)*ArcTan[a*x]^(n-1)/Sqrt[c+d*x^2],x] - 
  a^2*(m+2)/(m+1)*Int[x^(m+2)*ArcTan[a*x]^n/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_^m_*ArcCot[a_.*x_]^n_./Sqrt[c_+d_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[c+d*x^2]*ArcCot[a*x]^n/(c*(m+1)) + 
  a*n/(m+1)*Int[x^(m+1)*ArcCot[a*x]^(n-1)/Sqrt[c+d*x^2],x] - 
  a^2*(m+2)/(m+1)*Int[x^(m+2)*ArcCot[a*x]^n/Sqrt[c+d*x^2],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcTan[a*x]^n/(2*d*(p+1)) -
  n/(2*a*(p+1))*Int[(c+d*x^2)^p*ArcTan[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n,p] && p<-1 && n>0


Int[x_*(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  (c+d*x^2)^(p+1)*ArcCot[a*x]^n/(2*d*(p+1)) +
  n/(2*a*(p+1))*Int[(c+d*x^2)^p*ArcCot[a*x]^(n-1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n,p] && p<-1 && n>0


Int[x_*(c_+d_.*x_^2)^p_./ArcTan[a_.*x_]^2,x_Symbol] :=
  -x*(c+d*x^2)^(p+1)/(a*c*ArcTan[a*x]) + 
  c^p/a^2*Subst[Int[Expand[TrigReduce[(p+2-(p+1)*Cos[2*x])/(x*Cos[x]^(2*(p+2)))]],x],x,ArcTan[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[2*p] && p<-1 && (IntegerQ[p] || PositiveQ[c])


(* Int[x_*(c_+d_.*x_^2)^p_./ArcCot[a_.*x_]^2,x_Symbol] :=
  -x*(c+d*x^2)^(p+1)/(a*c*ArcCot[a*x]) - 
  (-c)^p/a^2*Subst[Int[Expand[TrigReduce[(p+2+(p+1)*Cos[2*x])/(x*Sin[x]^(2*(p+2)))]],x],x,ArcCot[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[2*p] && p<-1 && (IntegerQ[p] || PositiveQ[c]) *)


Int[x_*(c_+d_.*x_^2)^p_/ArcTan[a_.*x_]^2,x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[x*(1+a^2*x^2)^p/ArcTan[a*x]^2,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[p+1/2] && p<-1 && Not[PositiveQ[c]]


Int[x_*(c_+d_.*x_^2)^p_/ArcCot[a_.*x_]^2,x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[x*(1+a^2*x^2)^p/ArcCot[a*x]^2,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegerQ[p+1/2] && p<-1 && Not[PositiveQ[c]]


Int[x_*ArcTan[a_.*x_]^n_/(c_+d_.*x_^2)^2,x_Symbol] :=
  x*ArcTan[a*x]^(n+1)/(a*c*(n+1)*(c+d*x^2)) -
  (1-a^2*x^2)*ArcTan[a*x]^(n+2)/(d*(n+1)*(n+2)*(c+d*x^2)) -
  4/((n+1)*(n+2))*Int[x*ArcTan[a*x]^(n+2)/(c+d*x^2)^2,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n<-1 && n!=-2


Int[x_*ArcCot[a_.*x_]^n_/(c_+d_.*x_^2)^2,x_Symbol] :=
  -x*ArcCot[a*x]^(n+1)/(a*c*(n+1)*(c+d*x^2)) -
  (1-a^2*x^2)*ArcCot[a*x]^(n+2)/(d*(n+1)*(n+2)*(c+d*x^2)) -
  4/((n+1)*(n+2))*Int[x*ArcCot[a*x]^(n+2)/(c+d*x^2)^2,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n<-1 && n!=-2


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  x^m*(c+d*x^2)^(p+1)*ArcTan[a*x]^(n+1)/(a*c*(n+1)) -
  m/(a*(n+1))*Int[x^(m-1)*(c+d*x^2)^p*ArcTan[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n,p] && p<-1 && n<-1 && ZeroQ[m+2*p+2]


Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  -x^m*(c+d*x^2)^(p+1)*ArcCot[a*x]^(n+1)/(a*c*(n+1)) +
  m/(a*(n+1))*Int[x^(m-1)*(c+d*x^2)^p*ArcCot[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n,p] && p<-1 && n<-1 && ZeroQ[m+2*p+2]


Int[x_^m_.*(c_+d_.*x_^2)^p_/ArcTan[a_.*x_],x_Symbol] :=
  c^p/a^(m+1)*Subst[Int[Expand[TrigReduce[Sin[x]^m/(x*Cos[x]^(m+2*(p+1)))]],x],x,ArcTan[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,2*p] && (IntegerQ[p] || PositiveQ[c]) && 0<m<-(2*p+1)


(* Int[x_^m_.*(c_+d_.*x_^2)^p_/ArcCot[a_.*x_],x_Symbol] :=
  -(-c)^p/a^(m+1)*Subst[Int[Expand[TrigReduce[Cos[x]^m/(x*Sin[x]^(m+2*(p+1)))]],x],x,ArcCot[a*x]] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,2*p] && (IntegerQ[p] || PositiveQ[c]) && 0<m<-(2*p+1) *)


Int[x_^m_.*(c_+d_.*x_^2)^p_/ArcTan[a_.*x_],x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[x^m*(1+a^2*x^2)^p/ArcTan[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,p+1/2] && Not[PositiveQ[c]] && 0<m<-(2*p+1)


Int[x_^m_.*(c_+d_.*x_^2)^p_/ArcCot[a_.*x_],x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[x^m*(1+a^2*x^2)^p/ArcCot[a*x],x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,p+1/2] && Not[PositiveQ[c]] && 0<m<-(2*p+1)


Int[x_^m_*(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  1/d*Int[x^(m-2)*(c+d*x^2)^(p+1)*ArcTan[a*x]^n,x] -
  c/d*Int[x^(m-2)*(c+d*x^2)^p*ArcTan[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(c_+d_.*x_^2)^p_*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  1/d*Int[x^(m-2)*(c+d*x^2)^(p+1)*ArcCot[a*x]^n,x] -
  c/d*Int[x^(m-2)*(c+d*x^2)^p*ArcCot[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  1/c*Int[x^m*(c+d*x^2)^(p+1)*ArcTan[a*x]^n,x] -
  d/c*Int[x^(m+2)*(c+d*x^2)^p*ArcTan[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_*(c_+d_.*x_^2)^p_*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  1/c*Int[x^m*(c+d*x^2)^(p+1)*ArcCot[a*x]^n,x] -
  d/c*Int[x^(m+2)*(c+d*x^2)^p*ArcCot[a*x]^n,x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  x^m*(c+d*x^2)^(p+1)*ArcTan[a*x]^(n+1)/(a*c*(n+1)) - 
  m/(a*(n+1))*Int[x^(m-1)*(c+d*x^2)^p*ArcTan[a*x]^(n+1),x] - 
  a*(m+2*p+2)/(n+1)*Int[x^(m+1)*(c+d*x^2)^p*ArcTan[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n,p] && p<-1 && n<-1 && NonzeroQ[m+2*p+2]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  -x^m*(c+d*x^2)^(p+1)*ArcCot[a*x]^(n+1)/(a*c*(n+1)) + 
  m/(a*(n+1))*Int[x^(m-1)*(c+d*x^2)^p*ArcCot[a*x]^(n+1),x] + 
  a*(m+2*p+2)/(n+1)*Int[x^(m+1)*(c+d*x^2)^p*ArcCot[a*x]^(n+1),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m,n,p] && p<-1 && n<-1 && NonzeroQ[m+2*p+2]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
  Defer[Int][x^m*(c+d*x^2)^p*ArcTan[a*x]^n,x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[d-a^2*c]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcCot[a_.*x_]^n_.,x_Symbol] :=
  Defer[Int][x^m*(c+d*x^2)^p*ArcCot[a*x]^n,x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[d-a^2*c]


Int[ArcTanh[u_]*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*ArcTan[a*x]^n/(c+d*x^2),x] -
  1/2*Int[Log[1-u]*ArcTan[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+a*x))^2]


Int[ArcCoth[u_]*ArcCot[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*ArcCot[a*x]^n/(c+d*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*ArcCot[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+a*x))^2]


Int[ArcTanh[u_]*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*ArcTan[a*x]^n/(c+d*x^2),x] -
  1/2*Int[Log[1-u]*ArcTan[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-a*x))^2]


Int[ArcCoth[u_]*ArcCot[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*ArcCot[a*x]^n/(c+d*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*ArcCot[a*x]^n/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-a*x))^2]


Int[ArcTan[a_.*x_]^n_.*Log[u_]/(c_+d_.*x_^2),x_Symbol] :=
  I*ArcTan[a*x]^n*PolyLog[2,Together[1-u]]/(2*a*c) -
  n*I/2*Int[ArcTan[a*x]^(n-1)*PolyLog[2,Together[1-u]]/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I+a*x))^2]


Int[ArcCot[a_.*x_]^n_.*Log[u_]/(c_+d_.*x_^2),x_Symbol] :=
  I*ArcCot[a*x]^n*PolyLog[2,Together[1-u]]/(2*a*c) +
  n*I/2*Int[ArcCot[a*x]^(n-1)*PolyLog[2,Together[1-u]]/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I+a*x))^2]


Int[ArcTan[a_.*x_]^n_.*Log[u_]/(c_+d_.*x_^2),x_Symbol] :=
  -I*ArcTan[a*x]^n*PolyLog[2,Together[1-u]]/(2*a*c) +
  n*I/2*Int[ArcTan[a*x]^(n-1)*PolyLog[2,Together[1-u]]/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I-a*x))^2]


Int[ArcCot[a_.*x_]^n_.*Log[u_]/(c_+d_.*x_^2),x_Symbol] :=
  -I*ArcCot[a*x]^n*PolyLog[2,Together[1-u]]/(2*a*c) -
  n*I/2*Int[ArcCot[a*x]^(n-1)*PolyLog[2,Together[1-u]]/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I-a*x))^2]


Int[ArcTan[a_.*x_]^n_.*PolyLog[p_,u_]/(c_+d_.*x_^2),x_Symbol] :=
  -I*ArcTan[a*x]^n*PolyLog[p+1,u]/(2*a*c) +
  n*I/2*Int[ArcTan[a*x]^(n-1)*PolyLog[p+1,u]/(c+d*x^2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+a*x))^2]


Int[ArcCot[a_.*x_]^n_.*PolyLog[p_,u_]/(c_+d_.*x_^2),x_Symbol] :=
  -I*ArcCot[a*x]^n*PolyLog[p+1,u]/(2*a*c) -
  n*I/2*Int[ArcCot[a*x]^(n-1)*PolyLog[p+1,u]/(c+d*x^2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+a*x))^2]


Int[ArcTan[a_.*x_]^n_.*PolyLog[p_,u_]/(c_+d_.*x_^2),x_Symbol] :=
  I*ArcTan[a*x]^n*PolyLog[p+1,u]/(2*a*c) -
  n*I/2*Int[ArcTan[a*x]^(n-1)*PolyLog[p+1,u]/(c+d*x^2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-a*x))^2]


Int[ArcCot[a_.*x_]^n_.*PolyLog[p_,u_]/(c_+d_.*x_^2),x_Symbol] :=
  I*ArcCot[a*x]^n*PolyLog[p+1,u]/(2*a*c) +
  n*I/2*Int[ArcCot[a*x]^(n-1)*PolyLog[p+1,u]/(c+d*x^2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-a*x))^2]


Int[1/(ArcCot[a_.*x_]*ArcTan[a_.*x_]*(c_+d_.*x_^2)),x_Symbol] :=
  (-Log[ArcCot[a*x]]+Log[ArcTan[a*x]])/(a*c*ArcCot[a*x]+a*c*ArcTan[a*x]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]


Int[ArcCot[a_.*x_]^m_.*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  -ArcCot[a*x]^(m+1)*ArcTan[a*x]^n/(a*c*(m+1)) +
  n/(m+1)*Int[ArcCot[a*x]^(m+1)*ArcTan[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n] && 0<n<=m


Int[ArcTan[a_.*x_]^m_.*ArcCot[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
  ArcTan[a*x]^(m+1)*ArcCot[a*x]^n/(a*c*(m+1)) +
  n/(m+1)*Int[ArcTan[a*x]^(m+1)*ArcCot[a*x]^(n-1)/(c+d*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n] && 0<n<m


Int[ArcTan[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I*a*x]/(c+d*x^n),x] -
  I/2*Int[Log[1+I*a*x]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[d-a^2*c]]


Int[ArcCot[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I/(a*x)]/(c+d*x^n),x] -
  I/2*Int[Log[1+I/(a*x)]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[d-a^2*c]]


Int[x_*ArcTan[a_.*x_]^2*Log[c_+d_.*x_^2],x_Symbol] :=
  (c+d*x^2)*ArcTan[a*x]^2*Log[c+d*x^2]/(2*d) - 
  x^2*ArcTan[a*x]^2/2 - 
  1/a*Int[ArcTan[a*x]*Log[c+d*x^2],x] + 
  a*Int[x^2*ArcTan[a*x]/(1+a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c-d]


Int[x_*ArcCot[a_.*x_]^2*Log[c_+d_.*x_^2],x_Symbol] :=
  (c+d*x^2)*ArcCot[a*x]^2*Log[c+d*x^2]/(2*d) - 
  x^2*ArcCot[a*x]^2/2 + 
  1/a*Int[ArcCot[a*x]*Log[c+d*x^2],x] - 
  a*Int[x^2*ArcCot[a*x]/(1+a^2*x^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c-d]


Int[ArcTan[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcTan[a+b*x]/b - Log[1+(a+b*x)^2]/(2*b) /;
FreeQ[{a,b},x]


Int[ArcCot[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcCot[a+b*x]/b + Log[1+(a+b*x)^2]/(2*b) /;
FreeQ[{a,b},x]


Int[ArcTan[a_+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[ArcTan[x]^n,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1


Int[ArcCot[a_+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[ArcCot[x]^n,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1


Int[ArcTan[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][ArcTan[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcCot[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][ArcCot[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcTan[a_+b_.*x_]/x_,x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*x]/x,x] -
  I/2*Int[Log[1+I*a+I*b*x]/x,x] /;
FreeQ[{a,b},x]


Int[ArcCot[a_+b_.*x_]/x_,x_Symbol] :=
  I/2*Int[Log[1-I/(a+b*x)]/x,x] -
  I/2*Int[Log[1+I/(a+b*x)]/x,x] /;
FreeQ[{a,b},x]


Int[x_^m_.*ArcTan[a_+b_.*x_],x_Symbol] :=
  x^(m+1)*ArcTan[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)/(1+a^2+2*a*b*x+b^2*x^2),x] /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]


Int[x_^m_.*ArcCot[a_+b_.*x_],x_Symbol] :=
  x^(m+1)*ArcCot[a+b*x]/(m+1) +
  b/(m+1)*Int[x^(m+1)/(1+a^2+2*a*b*x+b^2*x^2),x] /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]


Int[x_^m_.*ArcTan[a_+b_.*x_]^n_,x_Symbol] :=
  1/b^(m+1)*Subst[Int[(x-a)^m*ArcTan[x]^n,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1 && PositiveIntegerQ[m]


Int[x_^m_.*ArcCot[a_+b_.*x_]^n_,x_Symbol] :=
  1/b^(m+1)*Subst[Int[(x-a)^m*ArcCot[x]^n,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1 && PositiveIntegerQ[m]


Int[x_^m_.*ArcTan[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcTan[a+b*x]^n,x] /;
FreeQ[{a,b,m},x] && IntegerQ[n] && n>1 && Not[PositiveIntegerQ[m]]


Int[x_^m_.*ArcCot[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcCot[a+b*x]^n,x] /;
FreeQ[{a,b,m},x] && IntegerQ[n] && n>1 && Not[PositiveIntegerQ[m]]


Int[x_^m_.*ArcTan[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcTan[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*ArcCot[a_+b_.*x_]^n_,x_Symbol] :=
  Defer[Int][x^m*ArcCot[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[PositiveIntegerQ[n]]


Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*x]/(c+d*x^n),x] -
  I/2*Int[Log[1+I*a+I*b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[(-I+a+b*x)/(a+b*x)]/(c+d*x^n),x] -
  I/2*Int[Log[(I+a+b*x)/(a+b*x)]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcTan[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcCot[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcTan[a_+b_.*x_^n_],x_Symbol] :=
  x*ArcTan[a+b*x^n] -
  b*n*Int[x^n/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
FreeQ[{a,b,n},x]


Int[ArcCot[a_+b_.*x_^n_],x_Symbol] :=
  x*ArcCot[a+b*x^n] +
  b*n*Int[x^n/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
FreeQ[{a,b,n},x]


Int[ArcTan[a_.+b_.*x_^n_]/x_,x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*x^n]/x,x] -
  I/2*Int[Log[1+I*a+I*b*x^n]/x,x] /;
FreeQ[{a,b,n},x]


Int[ArcCot[a_.+b_.*x_^n_]/x_,x_Symbol] :=
  I/2*Int[Log[1-I/(a+b*x^n)]/x,x] -
  I/2*Int[Log[1+I/(a+b*x^n)]/x,x] /;
FreeQ[{a,b,n},x]


Int[x_^m_.*ArcTan[a_+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*ArcTan[a+b*x^n]/(m+1) -
  b*n/(m+1)*Int[x^(m+n)/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n


Int[x_^m_.*ArcCot[a_+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*ArcCot[a+b*x^n]/(m+1) +
  b*n/(m+1)*Int[x^(m+n)/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n


Int[ArcTan[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*f^(c+d*x)],x] -
  I/2*Int[Log[1+I*a+I*b*f^(c+d*x)],x] /;
FreeQ[{a,b,c,d,f},x]


Int[ArcCot[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  I/2*Int[Log[1-I/(a+b*f^(c+d*x))],x] -
  I/2*Int[Log[1+I/(a+b*f^(c+d*x))],x] /;
FreeQ[{a,b,c,d,f},x] 


Int[x_^m_.*ArcTan[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  I/2*Int[x^m*Log[1-I*a-I*b*f^(c+d*x)],x] -
  I/2*Int[x^m*Log[1+I*a+I*b*f^(c+d*x)],x] /;
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0


Int[x_^m_.*ArcCot[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  I/2*Int[x^m*Log[1-I/(a+b*f^(c+d*x))],x] -
  I/2*Int[x^m*Log[1+I/(a+b*f^(c+d*x))],x] /;
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0


Int[u_.*ArcTan[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCot[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCot[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcTan[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  1/c*Log[ArcTan[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && ZeroQ[b+c^2]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  -1/c*Log[ArcCot[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && ZeroQ[b+c^2]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  ArcTan[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && ZeroQ[b+c^2] && NonzeroQ[m+1]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  -ArcCot[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && ZeroQ[b+c^2] && NonzeroQ[m+1]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcTan[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b+c^2] && ZeroQ[b*d-a*e]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcCot[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b+c^2] && ZeroQ[b*d-a*e]


Int[E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[a,x] && RationalQ[I*n]


Int[E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  4*(I-a*x)*E^(n*ArcTan[a*x])/(a*(n+2*I)*(I+a*x))*Hypergeometric2F1[2,1-I*n/2,2-I*n/2,-E^(2*I*ArcTan[a*x])] /;
FreeQ[{a,n},x] && Not[RationalQ[I*n]]


Int[x_^m_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[x^m*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,m,n},x]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1+d*x/c)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2+d^2] && (IntegerQ[p] || PositiveQ[c])


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(1+d*x/c)^p*Int[u*(1+d*x/c)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2+d^2] && Not[IntegerQ[p] || PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[c^2+a^2*d^2] && IntegerQ[p]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*c^p*Int[u*(1+d/(c*x))^p*(1-1/(I*a*x))^(I*n/2)/(1+1/(I*a*x))^(I*n/2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  Int[u*(c+d/x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  x^p*(c+d/x)^p/(1+c*x/d)^p*Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[p]]


Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcTan[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c]


Int[E^(n_*ArcTan[a_.*x_])/Sqrt[1+d_.*x_^2],x_Symbol] :=
  Int[1/(1-a*n*x),x] /;
FreeQ[{a,d,n},x] && ZeroQ[d-a^2] && ZeroQ[n^2+1]


Int[E^(n_*ArcTan[a_.*x_])/Sqrt[c_.+d_.*x_^2],x_Symbol] :=
  Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[E^(n*ArcTan[a*x])/Sqrt[1+a^2*x^2],x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+1] && NonzeroQ[c-1]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*a*p*x)*(c+d*x^2)^p*E^(n*ArcTan[a*x])/(2*a*p*(2*p+1)) /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+4*p^2] && NonzeroQ[p+1/2]


(* Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*a*p*x)*(c+d*x^2)^p*E^(n*ArcTan[a*x])/(2*a*p*(2*p+1)) + 
  c*(n^2+4*p^2)/(2*p*(2*p+1))*Int[(c+d*x^2)^(p-1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n^2+4*p^2] && RationalQ[p] && p>0 *)


Int[E^(n_*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  1/c^(3/2)*Int[1/((1+a*n*x)*(1-a*n*x)^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+1] && PositiveQ[c]


Int[E^(n_*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  Sqrt[1+a^2*x^2]/(c*Sqrt[c+d*x^2])*Int[E^(n*ArcTan[a*x])/(1+a^2*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+1] && Not[PositiveQ[c]]


Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n+a*x)*E^(n*ArcTan[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n^2+9] && NonzeroQ[n^2+1]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (n-2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*c*(n^2+4*(p+1)^2)) + 
  2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n^2+4*p^2] && RationalQ[p] && p<-1 && p!=-3/2 && NonzeroQ[n^2+4*(p+1)^2] && 
  IntegerQ[2*p]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[(1+a^2*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c]) && OddQ[I*n]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c]) && Not[OddQ[I*n]] && 
  (RationalQ[I*n,p] || PositiveIntegerQ[p-I*n/2] || PositiveIntegerQ[p+I*n/2])


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  1/c^(I*n/2)*Int[(c+d*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && EvenQ[I*n] && RationalQ[p]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && PositiveIntegerQ[p+1/2] && RationalQ[I*n]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && NegativeIntegerQ[p-1/2] && RationalQ[I*n]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(1+a^2*x^2)^p*Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[p+1/2]] && 
  (RationalQ[n,p] || PositiveIntegerQ[p-n/2] || PositiveIntegerQ[p+n/2])


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+a^2*c*x^2)^(p+1)*E^(n*ArcTan[a*x])/(2*a*c*n)*(1+E^(n/(p+1)*ArcTan[a*x]))^(2*(p+1))*
    Hypergeometric2F1[2*(p+1),2*(p+1),2*p+3,-E^(n/(p+1)*ArcTan[a*x])] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+4*(p+1)^2] && Not[IntegerQ[2*p]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  4^(p+1)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*c*(n+2*I*(p+1)))*(1/(1-I*a*x))^(2*(p+1))*
    Hypergeometric2F1[p-I*n/2+1,2*(p+1),p-I*n/2+2,-E^(2*I*ArcTan[a*x])] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && NonzeroQ[n^2+4*(p+1)^2] && Not[NegativeIntegerQ[2*p+1]] && Not[IntegerQ[p-I*n/2]]


Int[x_*E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcTan[a*x])/(a^2*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[OddQ[I*n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a^2*c*(n^2+4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<=-1 && p!=-3/2 && NonzeroQ[n^2+4*(p+1)^2] && Not[OddQ[I*n]]


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a^3*c*n^2*(n^2+1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2-2*(p+1)] && NonzeroQ[n^2+1]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a^3*c*(n^2+4*(p+1)^2)) + 
  (n^2-2*(p+1))/(a^2*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<=-1 && NonzeroQ[n^2-2*(p+1)] && NonzeroQ[n^2+4*(p+1)^2] && Not[OddQ[I*n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p/a^(m+1)*Subst[Int[E^(n*x)*Tan[x]^(m+2*(p+1))/Sin[x]^(2*(p+1)),x],x,ArcTan[a*x]] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && IntegerQ[m] && RationalQ[p] && 3<=m<=-2(p+1) && IntegerQ[2*p] && (IntegerQ[p] || PositiveQ[c])


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1+a^2*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c]) && OddQ[I*n] && 
  (Not[RationalQ[p]] || Not[RationalQ[m]] || ZeroQ[I*n-1] && NonzeroQ[p+1])


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  1/c^(I*n/2)*Int[x^m*(c+d*x^2)^(p+I*n/2)/(1+a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && IntegerQ[I*n/2] && 
  (ZeroQ[m-1] || Not[IntegerQ[p+1/2]])


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c])


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/(Sqrt[1-I*a*x]*Sqrt[1+I*a*x])*Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && IntegerQ[I*n/2] && PositiveIntegerQ[p+1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1-I*a*x]*Sqrt[1+I*a*x]/Sqrt[c+d*x^2]*Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && IntegerQ[I*n/2] && NegativeIntegerQ[p-1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && Not[IntegerQ[I*n/2]] && PositiveIntegerQ[p+1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && Not[IntegerQ[I*n/2]] && NegativeIntegerQ[p-1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(1+a^2*x^2)^p*Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p+1/2]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[c-a^2*d] && IntegerQ[p]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-I/(a*x))^p*(1+I/(a*x))^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/((1-I*a*x)^p*(1+I*a*x)^p)*Int[u/x^(2*p)*(1-I*a*x)^p*(1+I*a*x)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/(1+a^2*x^2)^p*Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[p]] && Not[IntegerQ[I*n/2]]


Int[u_.*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  (-1)^(I*n/2)*Int[u*E^(-n*ArcTan[a*x]),x] /;
FreeQ[a,x] && IntegerQ[I*n/2]


Int[E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[I*n/2]]


Int[x_^m_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[I*n/2]] && IntegerQ[m]


Int[x_^m_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[m]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c^2+d^2] && Not[IntegerQ[I*n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(x^p*(1+c/(d*x))^p)*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2+d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]


Int[(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c])


Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegerQ[m]


Int[(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[x_^m_*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[u*(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  -E^(n*ArcCot[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c]


Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(n-a*x)*E^(n*ArcCot[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[OddQ[I*n]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -(n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a*c*(n^2+4*(p+1)^2)) + 
  2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<-1 && p!=-3/2 && NonzeroQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_*E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1+a*n*x)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[OddQ[I*n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (2*(p+1)-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+4*(p+1)^2)) + 
  n*(2*p+3)/(a*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<=-1 && p!=-3/2 && NonzeroQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*n^2*(n^2+1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2-2*(p+1)] && NonzeroQ[n^2+1]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*(n^2+4*(p+1)^2)) + 
  (n^2-2*(p+1))/(a^2*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<=-1 && NonzeroQ[n^2-2*(p+1)] && NonzeroQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p/a^(m+1)*Subst[Int[E^(n*x)*Cot[x]^(m+2*(p+1))/Cos[x]^(2*(p+1)),x],x,ArcCot[a*x]] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && IntegerQ[m] && 3<=m<=-2(p+1) && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[I*n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(x^(2*p)*(1+1/(a^2*x^2))^p)*Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  c^p/(I*a)^(2*p)*Int[u/x^(2*p)*(-1+I*a*x)^(p-I*n/2)*(1+I*a*x)^(p+I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegersQ[2*p,p+I*n/2]


Int[(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^2,x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]]


Int[x_^m_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]] && 
  IntegerQ[m]


Int[x_^m_*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]] && 
  Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x^2)^p/(1+1/(a^2*x^2))^p*Int[u*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,n},x]


Int[x_^m_*E^(n_*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(I^m*n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/(I*n))*(1-I*a*c-(1+I*a*c)*x^(2/(I*n)))^m/(1+x^(2/(I*n)))^(m+2),x],x,
      (1-I*c*(a+b*x))^(I*n/2)/(1+I*c*(a+b*x))^(I*n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[I*n] && -1<I*n<1


Int[x_^m_.*E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[x^m*(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,m,n},x] && Not[NegativeIntegerQ[m] && RationalQ[I*n] && -1<I*n<1]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
  (c/(1+a^2))^p*Int[u*(1-I*a-I*b*x)^(p+I*n/2)*(1+I*a+I*b*x)^(p-I*n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c-e(1+a^2)] && (IntegerQ[p] || PositiveQ[c/(1+a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p*Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c-e(1+a^2)] && Not[IntegerQ[p] || PositiveQ[c/(1+a^2)]]


Int[u_.*E^(n_*ArcCot[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (-1)^(I*n/2)*Int[u*E^(-n*ArcTan[c*(a+b*x)]),x] /;
FreeQ[{a,b,c},x] && IntegerQ[I*n/2]


Int[E^(n_.*ArcCot[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (I*c*(a+b*x))^(I*n/2)*(1+1/(I*c*(a+b*x)))^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2)*
    Int[(1+I*a*c+I*b*c*x)^(I*n/2)/(-1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[I*n/2]]


Int[x_^m_*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(I^m*n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/(I*n))*(1+I*a*c+(1-I*a*c)*x^(2/(I*n)))^m/(-1+x^(2/(I*n)))^(m+2),x],x,
      (1+1/(I*c*(a+b*x)))^(I*n/2)/(1-1/(I*c*(a+b*x)))^(I*n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[I*n] && -1<I*n<1


Int[x_^m_.*E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (I*c*(a+b*x))^(I*n/2)*(1+1/(I*c*(a+b*x)))^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2)*
    Int[x^m*(1+I*a*c+I*b*c*x)^(I*n/2)/(-1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[I*n/2]] && Not[NegativeIntegerQ[m] && RationalQ[I*n] && -1<I*n<1]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
  (c/(1+a^2))^p*((I*a+I*b*x)/(1+I*a+I*b*x))^(I*n/2)*((1+I*a+I*b*x)/(I*a+I*b*x))^(I*n/2)*
    ((1-I*a-I*b*x)^(I*n/2)/(-1+I*a+I*b*x)^(I*n/2))*
    Int[u*(1-I*a-I*b*x)^(p-I*n/2)*(1+I*a+I*b*x)^(p+I*n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c-e(1+a^2)] && 
  (IntegerQ[p] || PositiveQ[c/(1+a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p*Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c-e(1+a^2)] && 
  Not[IntegerQ[p] || PositiveQ[c/(1+a^2)]]


Int[u_.*E^(n_.*ArcTan[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcCot[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*E^(n_.*ArcCot[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcTan[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*ArcTan[v_+s_.*Sqrt[w_]],x_Symbol] :=
  Pi*s/4*Int[u,x] + 1/2*Int[u*ArcTan[v],x] /;
ZeroQ[s^2-1] && ZeroQ[w-(v^2+1)]


Int[u_.*ArcCot[v_+s_.*Sqrt[w_]],x_Symbol] :=
  Pi*s/4*Int[u,x] - 1/2*Int[u*ArcTan[v],x] /;
ZeroQ[s^2-1] && ZeroQ[w-(v^2+1)]


Int[(c_.+d_.*x_^2)^n_*ArcTan[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcTan[a*x],u,x] - 
  a*Int[Dist[1/(1+a^2*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[2*n] && n<=-1


Int[(c_.+d_.*x_^2)^n_*ArcCot[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcCot[a*x],u,x] + 
  a*Int[Dist[1/(1+a^2*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[2*n] && n<=-1


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcTan[a+b*x]]/(1+(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Tan[x]/b,x],x],x,ArcTan[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTan && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTan && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcCot[a+b*x]]/(1+(a+b*x)^2),x]",
		   "-Subst[Int[f[-a/b+Cot[x]/b,x],x],x,ArcCot[a+b*x]]/b",Hold[
  -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCot && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCot && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


Int[ArcTan[u_],x_Symbol] :=
  x*ArcTan[u] -
  Int[SimplifyIntegrand[x*D[u,x]/(1+u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[ArcCot[u_],x_Symbol] :=
  x*ArcCot[u] +
  Int[SimplifyIntegrand[x*D[u,x]/(1+u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[x_^m_.*ArcTan[u_],x_Symbol] :=
  x^(m+1)*ArcTan[u]/(m+1) -
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/(1+u^2),x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	FalseQ[PowerVariableExpn[u,m+1,x]]


Int[x_^m_.*ArcCot[u_],x_Symbol] :=
  x^(m+1)*ArcCot[u]/(m+1) +
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/(1+u^2),x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	FalseQ[PowerVariableExpn[u,m+1,x]]


Int[v_*ArcTan[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[ArcTan[u],w,x] -
  Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x] && 
	Not[MatchQ[v, x^m_. /; FreeQ[m,x]]] &&
	FalseQ[FunctionOfLinear[v*ArcTan[u],x]]


Int[v_*ArcCot[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[ArcCot[u],w,x] +
  Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x] && 
	Not[MatchQ[v, x^m_. /; FreeQ[m,x]]] &&
	FalseQ[FunctionOfLinear[v*ArcCot[u],x]]


Int[ArcTan[v_]*Log[w_],x_Symbol] :=
  x*ArcTan[v]*Log[w] - 
  Int[SimplifyIntegrand[x*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[x*ArcTan[v]*D[w,x]/w,x],x] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[ArcCot[v_]*Log[w_],x_Symbol] :=
  x*ArcCot[v]*Log[w] + 
  Int[SimplifyIntegrand[x*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[x*ArcCot[v]*D[w,x]/w,x],x] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*ArcTan[v_]*Log[w_],x_Symbol] :=
  Module[{z=Block[{ShowSteps=False,StepCounter=Null}, Int[u,x]]},  
  Dist[ArcTan[v]*Log[w],z,x] - 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[z*ArcTan[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*ArcCot[v_]*Log[w_],x_Symbol] :=
  Module[{z=Block[{ShowSteps=False,StepCounter=Null}, Int[u,x]]},  
  Dist[ArcCot[v]*Log[w],z,x] + 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[z*ArcCot[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[ArcSec[a_.*x_],x_Symbol] :=
  x*ArcSec[a*x] - 1/a*Int[1/(x*Sqrt[1-1/(a^2*x^2)]),x] /;
FreeQ[a,x]


Int[ArcCsc[a_.*x_],x_Symbol] :=
  x*ArcCsc[a*x] + 1/a*Int[1/(x*Sqrt[1-1/(a^2*x^2)]),x] /;
FreeQ[a,x]


Int[ArcSec[a_.*x_]^n_,x_Symbol] :=
  1/a*Subst[Int[x^n*Sec[x]*Tan[x],x],x,ArcSec[a*x]] /;
FreeQ[{a,n},x]


Int[ArcCsc[a_.*x_]^n_,x_Symbol] :=
  -1/a*Subst[Int[x^n*Csc[x]*Cot[x],x],x,ArcCsc[a*x]] /;
FreeQ[{a,n},x]


Int[ArcSec[a_.*x_]/x_,x_Symbol] :=
  1/2*I*ArcSec[a*x]^2 - 
  ArcSec[a*x]*Log[2/(1-I*a*x*Sqrt[1-1/(a^2*x^2)])] + 
  1/2*I*PolyLog[2,1-2/(1-I*a*x*Sqrt[1-1/(a^2*x^2)])] /;
FreeQ[a,x]


Int[ArcCsc[a_.*x_]/x_,x_Symbol] :=
  -1/2*I*ArcCsc[a*x]^2 - 
  ArcCsc[a*x]*Log[2/(1-I*a*x*Sqrt[1-1/(a^2*x^2)])] - 
  1/2*I*PolyLog[2,1-2/(1-I*a*x*Sqrt[1-1/(a^2*x^2)])] /;
FreeQ[a,x]


Int[x_^m_.*ArcSec[a_.*x_],x_Symbol] :=
  x^(m+1)*ArcSec[a*x]/(m+1) - 
  1/(a*(m+1))*Int[x^(m-1)/Sqrt[1-1/(a*x)^2],x] /;
FreeQ[{a,m},x] && NonzeroQ[m+1]


Int[x_^m_.*ArcCsc[a_.*x_],x_Symbol] :=
  x^(m+1)*ArcCsc[a*x]/(m+1) +
  1/(a*(m+1))*Int[x^(m-1)/Sqrt[1-1/(a^2*x^2)],x] /;
FreeQ[{a,m},x] && NonzeroQ[m+1]


Int[x_^m_.*ArcSec[a_.*x_]^n_,x_Symbol] :=
  1/a^(m+1)*Subst[Int[x^n*Sec[x]^(m+1)*Tan[x],x],x,ArcSec[a*x]] /;
FreeQ[{a,n},x] && IntegerQ[m]


Int[x_^m_.*ArcCsc[a_.*x_]^n_,x_Symbol] :=
  -1/a^(m+1)*Subst[Int[x^n*Csc[x]^(m+1)*Cot[x],x],x,ArcCsc[a*x]] /;
FreeQ[{a,n},x] && IntegerQ[m]


Int[ArcSec[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcSec[a+b*x]/b - 
  Int[1/((a+b*x)*Sqrt[1-1/(a+b*x)^2]),x] /;
FreeQ[{a,b},x]


Int[ArcCsc[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcCsc[a+b*x]/b + 
  Int[1/((a+b*x)*Sqrt[1-1/(a+b*x)^2]),x] /;
FreeQ[{a,b},x]


Int[ArcSec[a_+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[x^n*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcCsc[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[x^n*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcSec[a_+b_.*x_]/x_,x_Symbol] :=
  ArcSec[a+b*x]*Log[1-(1-Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] + 
  ArcSec[a+b*x]*Log[1-(1+Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] - 
  ArcSec[a+b*x]*Log[1+E^(2*I*ArcSec[a+b*x])] - 
  I*PolyLog[2,(1-Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] - 
  I*PolyLog[2,(1+Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] + 
  1/2*I*PolyLog[2,-E^(2*I*ArcSec[a+b*x])] /;
FreeQ[{a,b},x]


Int[ArcCsc[a_+b_.*x_]/x_,x_Symbol] :=
  I*ArcCsc[a+b*x]^2 + 
  ArcCsc[a+b*x]*Log[1-I*(1-Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  ArcCsc[a+b*x]*Log[1-I*(1+Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] - 
  ArcCsc[a+b*x]*Log[1-E^(2*I*ArcCsc[a+b*x])] + 
  I*PolyLog[2,I*(1-Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  I*PolyLog[2,I*(1+Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  1/2*I*PolyLog[2,E^(2*I*ArcCsc[a+b*x])] /;
FreeQ[{a,b},x]


Int[x_^m_.*ArcSec[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcSec[a+b*x]/(b^(m+1)*(m+1)) - 
  1/(b^(m+1)*(m+1))*Subst[Int[(((-a)*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1-x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NonzeroQ[m+1]


Int[x_^m_.*ArcCsc[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcCsc[a+b*x]/(b^(m+1)*(m+1)) + 
  1/(b^(m+1)*(m+1))*Subst[Int[(((-a)*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1-x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NonzeroQ[m+1]


Int[x_^m_.*ArcSec[a_+b_.*x_]^n_,x_Symbol] :=
  1/b^(m+1)*Subst[Int[x^n*(-a+Sec[x])^m*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,n},x] && IntegerQ[m]


Int[x_^m_.*ArcCsc[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b^(m+1)*Subst[Int[x^n*(-a+Csc[x])^m*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,n},x] && PositiveIntegerQ[m]


Int[x_^m_.*ArcSec[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*ArcSec[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*ArcCsc[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*ArcCsc[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[u_.*ArcSec[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCos[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCsc[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSin[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*f_^(c_.*ArcSec[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[ReplaceAll[u,x->-a/b+Sec[x]/b]*f^(c*x^n)*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[u_.*f_^(c_.*ArcCsc[a_.+b_.*x_]^n_.),x_Symbol] :=
  -1/b*Subst[Int[ReplaceAll[u,x->-a/b+Csc[x]/b]*f^(c*x^n)*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[ArcSec[u_],x_Symbol] :=
  x*ArcSec[u] -
  Int[SimplifyIntegrand[x*D[u,x]/(u^2*Sqrt[1-1/u^2]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCsc[u_],x_Symbol] :=
  x*ArcCsc[u] +
  Int[SimplifyIntegrand[x*D[u,x]/(u^2*Sqrt[1-1/u^2]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[x_^m_.*ArcSec[u_],x_Symbol] :=
  x^(m+1)*ArcSec[u]/(m+1) -
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/(u^2*Sqrt[1-1/u^2]),x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	Not[FunctionOfExponentialQ[u,x]]


Int[x_^m_.*ArcCsc[u_],x_Symbol] :=
  x^(m+1)*ArcCsc[u]/(m+1) +
  1/(m+1)*Int[SimplifyIntegrand[x^(m+1)*D[u,x]/(u^2*Sqrt[1-1/u^2]),x],x] /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	Not[FunctionOfExponentialQ[u,x]]


Int[v_*ArcSec[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[ArcSec[u],w,x] -
  Int[SimplifyIntegrand[w*D[u,x]/(u^2*Sqrt[1-1/u^2]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x]


Int[v_*ArcCsc[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[ArcCsc[u],w,x] +
  Int[SimplifyIntegrand[w*D[u,x]/(u^2*Sqrt[1-1/u^2]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x]
