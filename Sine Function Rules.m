(* ::Package:: *)

(* ::Section:: *)
(*Trig Function Rules*)


(* ::Subsection::Closed:: *)
(*1 (c trig^m)^n*)


Int[(c_.*sin[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  -Cot[a+b*x]*(c*Sin[a+b*x]^2)^n/(2*b*n) + 
  c*(2*n-1)/(2*n)*Int[(c*Sin[a+b*x]^2)^(n-1),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_.*cos[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  Tan[a+b*x]*(c*Cos[a+b*x]^2)^n/(2*b*n) + 
  c*(2*n-1)/(2*n)*Int[(c*Cos[a+b*x]^2)^(n-1),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_.*sin[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  Cot[a+b*x]*(c*Sin[a+b*x]^2)^(n+1)/(b*c*(2*n+1)) + 
  2*(n+1)/(c*(2*n+1))*Int[(c*Sin[a+b*x]^2)^(n+1),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_.*cos[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  -Tan[a+b*x]*(c*Cos[a+b*x]^2)^(n+1)/(b*c*(2*n+1)) + 
  2*(n+1)/(c*(2*n+1))*Int[(c*Cos[a+b*x]^2)^(n+1),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(sec[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  1/b*Subst[Int[(1+x^2)^(n-1),x],x,Tan[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[(csc[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  -1/b*Subst[Int[(1+x^2)^(n-1),x],x,Cot[a+b*x]] /;
FreeQ[{a,b,n},x]


(* Int[(c_.*sec[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  1/b*Subst[Int[(c*(1+x^2))^n/(1+x^2),x],x,Tan[a+b*x]] /;
FreeQ[{a,b,c,n},x] *)


(* Int[(c_.*csc[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  -1/b*Subst[Int[(c*(1+x^2))^n/(1+x^2),x],x,Cot[a+b*x]] /;
FreeQ[{a,b,c,n},x] *)


Int[(c_.*(d_.*F_[a_.+b_.*x_])^m_)^n_,x_Symbol] :=
  Module[{u=ActivateTrig[F[a+b*x]]},
  c^(n-1/2)*(d*FreeFactors[u,x])^(m*(n-1/2))*Sqrt[c*(d*u)^m]/NonfreeFactors[u,x]^(m/2)*Int[NonfreeFactors[u,x]^(m*n),x]] /;
FreeQ[{a,b,c,d,m},x] && InertTrigQ[F] && PositiveIntegerQ[n+1/2]


Int[(c_.*(d_.*F_[a_.+b_.*x_])^m_)^n_,x_Symbol] :=
  Module[{u=ActivateTrig[F[a+b*x]]},
  c^(n+1/2)*(d*FreeFactors[u,x])^(m*(n+1/2))*NonfreeFactors[u,x]^(m/2)/Sqrt[c*(d*u)^m]*Int[NonfreeFactors[u,x]^(m*n),x]] /;
FreeQ[{a,b,c,d,m},x] && InertTrigQ[F] && NegativeIntegerQ[n-1/2]


Int[(c_.*(d_.*F_[a_.+b_.*x_])^m_)^n_,x_Symbol] :=
  Module[{u=ActivateTrig[F[a+b*x]]},
  (c*(d*u)^m)^n/NonfreeFactors[u,x]^(m*n)*Int[NonfreeFactors[u,x]^(m*n),x]] /;
FreeQ[{a,b,c,d,m,n},x] && InertTrigQ[F] && Not[IntegerQ[n+1/2]]


(* ::Subsection::Closed:: *)
(*2 (c trig)^m (d trig)^n*)


Int[(c_.*sin[a_.+b_.*x_])^m_.*cos[a_.+b_.*x_],x_Symbol] :=
  (c*Sin[a+b*x])^(m+1)/(b*c*(m+1)) /;
FreeQ[{a,b,c,m},x] && NonzeroQ[m+1]


Int[(c_.*cos[a_.+b_.*x_])^m_.*sin[a_.+b_.*x_],x_Symbol] :=
  -(c*Cos[a+b*x])^(m+1)/(b*c*(m+1)) /;
FreeQ[{a,b,c,m},x] && NonzeroQ[m+1]


Int[sin[a_.+b_.*x_]*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(d*Sec[a+b*x])^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,d,n},x] && NonzeroQ[n-1]


Int[cos[a_.+b_.*x_]*(d_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(d*Csc[a+b*x])^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,d,n},x] && NonzeroQ[n-1]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^(m+1)*(d*Cos[a+b*x])^(n+1)/(b*c*d*(m+1)) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m+n+2] && NonzeroQ[m+1]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c*d*(c*Csc[a+b*x])^(m-1)*(d*Sec[a+b*x])^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m+n-2] && NonzeroQ[n-1]


Int[(c_.*sin[a_.+b_.*x_])^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[(c*x)^m*(1-x^2)^((n-1)/2),x],x,Sin[a+b*x]] /;
FreeQ[{a,b,c,m},x] && OddQ[n] && Not[OddQ[m] && 0<m<n]


Int[sin[a_.+b_.*x_]^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  -1/b*Subst[Int[(d*x)^n*(1-x^2)^((m-1)/2),x],x,Cos[a+b*x]] /;
FreeQ[{a,b,d,n},x] && OddQ[m] && Not[OddQ[n] && 0<n<=m]


Int[(c_.*csc[a_.+b_.*x_])^m_*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  -1/(b*c^(n-1))*Subst[Int[(c*x)^(m+n-1)/(-1+x^2)^((n+1)/2),x],x,Csc[a+b*x]] /;
FreeQ[{a,b,c,m},x] && OddQ[n] && Not[OddQ[m] && 0<m<n] && Not[IntegerQ[m]]


Int[(c_.*sec[a_.+b_.*x_])^m_*csc[a_.+b_.*x_]^n_,x_Symbol] :=
  1/(b*c^(n-1))*Subst[Int[(c*x)^(m+n-1)/(-1+x^2)^((n+1)/2),x],x,Sec[a+b*x]] /;
FreeQ[{a,b,c,m},x] && OddQ[n] && Not[OddQ[m] && 0<m<=n] && Not[IntegerQ[m]]


Int[(c_.*csc[a_.+b_.*x_])^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -c^(n+1)/b*Subst[Int[(c*x)^(m-n-1)*(-1+x^2)^((n-1)/2),x],x,Csc[a+b*x]] /;
FreeQ[{a,b,c,m},x] && OddQ[n] && Not[OddQ[m] && 0<m<n] && Not[IntegerQ[m]]


Int[(c_.*sec[a_.+b_.*x_])^m_*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  c^(n+1)/b*Subst[Int[(c*x)^(m-n-1)*(-1+x^2)^((n-1)/2),x],x,Sec[a+b*x]] /;
FreeQ[{a,b,c,m},x] && OddQ[n] && Not[OddQ[m] && 0<m<=n] && Not[IntegerQ[m]]


Int[csc[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[(1+x^2)^((m+n)/2-1)/x^m,x],x,Tan[a+b*x]] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && EvenQ[m+n]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*(c*Sin[a+b*x])^(m-1)*(d*Cos[a+b*x])^(n+1)/(b*d*(n+1)) + 
  c^2*(m-1)/(d^2*(n+1))*Int[(c*Sin[a+b*x])^(m-2)*(d*Cos[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && n<-1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Sin[a+b*x])^(m+1)*(d*Cos[a+b*x])^(n-1)/(b*c*(m+1)) + 
  d^2*(n-1)/(c^2*(m+1))*Int[(c*Sin[a+b*x])^(m+2)*(d*Cos[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && n>1


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*(c*Csc[a+b*x])^(m-1)*(d*Sec[a+b*x])^(n+1)/(b*d*(m-1)) + 
  c^2*(n+1)/(d^2*(m-1))*Int[(c*Csc[a+b*x])^(m-2)*(d*Sec[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && n<-1


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Csc[a+b*x])^(m+1)*(d*Sec[a+b*x])^(n-1)/(b*c*(n-1)) + 
  d^2*(m+1)/(c^2*(n-1))*Int[(c*Csc[a+b*x])^(m+2)*(d*Sec[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && n>1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c*d*(c*Sin[a+b*x])^(m-1)*(d*Sec[a+b*x])^(n-1)/(b*(n-1)) - 
  c^2*d^2*(m-1)/(n-1)*Int[(c*Sin[a+b*x])^(m-2)*(d*Sec[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && n>1


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*d*(c*Cos[a+b*x])^(m-1)*(d*Csc[a+b*x])^(n-1)/(b*(n-1)) - 
  c^2*d^2*(m-1)/(n-1)*Int[(c*Cos[a+b*x])^(m-2)*(d*Csc[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && n>1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*(c*Sin[a+b*x])^(m-1)*(d*Cos[a+b*x])^(n+1)/(b*d*(m+n)) + 
  c^2*(m-1)/(m+n)*Int[(c*Sin[a+b*x])^(m-2)*(d*Cos[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n] && RationalQ[n]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Sin[a+b*x])^(m+1)*(d*Cos[a+b*x])^(n-1)/(b*c*(m+n)) + 
  d^2*(n-1)/(m+n)*Int[(c*Sin[a+b*x])^m*(d*Cos[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n] && RationalQ[m]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  -c*d*(c*Csc[a+b*x])^(m-1)*(d*Sec[a+b*x])^(n-1)/(b*(m-1)) + 
  c^2*(m+n-2)/(m-1)*Int[(c*Csc[a+b*x])^(m-2)*(d*Sec[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-2] && Not[EvenQ[m] && OddQ[n] && n>1] && RationalQ[n]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c*d*(c*Csc[a+b*x])^(m-1)*(d*Sec[a+b*x])^(n-1)/(b*(n-1)) + 
  d^2*(m+n-2)/(n-1)*Int[(c*Csc[a+b*x])^m*(d*Sec[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-2] && RationalQ[m]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*d*(c*Sin[a+b*x])^(m-1)*(d*Sec[a+b*x])^(n-1)/(b*(m-n)) + 
  c^2*(m-1)/(m-n)*Int[(c*Sin[a+b*x])^(m-2)*(d*Sec[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && NonzeroQ[m-n] && RationalQ[n]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  c*d*(c*Cos[a+b*x])^(m-1)*(d*Csc[a+b*x])^(n-1)/(b*(m-n)) + 
  c^2*(m-1)/(m-n)*Int[(c*Cos[a+b*x])^(m-2)*(d*Csc[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && NonzeroQ[m-n] && RationalQ[n]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^(m+1)*(d*Cos[a+b*x])^(n+1)/(b*c*d*(m+1)) + 
  (m+n+2)/(c^2*(m+1))*Int[(c*Sin[a+b*x])^(m+2)*(d*Cos[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+2] && RationalQ[n]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Sin[a+b*x])^(m+1)*(d*Cos[a+b*x])^(n+1)/(b*c*d*(n+1)) + 
  (m+n+2)/(d^2*(n+1))*Int[(c*Sin[a+b*x])^m*(d*Cos[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+2] && RationalQ[m]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  d*(c*Csc[a+b*x])^(m+1)*(d*Sec[a+b*x])^(n-1)/(b*c*(m+n)) + 
  (m+1)/(c^2*(m+n))*Int[(c*Csc[a+b*x])^(m+2)*(d*Sec[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n] && RationalQ[n]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*(c*Csc[a+b*x])^(m-1)*(d*Sec[a+b*x])^(n+1)/(b*d*(m+n)) + 
  (n+1)/(d^2*(m+n))*Int[(c*Csc[a+b*x])^m*(d*Sec[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n] && RationalQ[m]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Sin[a+b*x])^(m+1)*(d*Sec[a+b*x])^(n-1)/(b*c*(m+1)) + 
  (m-n+2)/(c^2*(m+1))*Int[(c*Sin[a+b*x])^(m+2)*(d*Sec[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m-n+2] && RationalQ[n]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Cos[a+b*x])^(m+1)*(d*Csc[a+b*x])^(n-1)/(b*c*(m+1)) + 
  (m-n+2)/(c^2*(m+1))*Int[(c*Cos[a+b*x])^(m+2)*(d*Csc[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m-n+2] && RationalQ[n]


Int[1/(Sqrt[c_.*sin[a_.+b_.*x_]]*Sqrt[d_.*cos[a_.+b_.*x_]]),x_Symbol] :=
  -2*(-1)^(3/4)*Sec[a+b*x]/(b*c*Rt[d/c,2]*Sqrt[Sec[a+b*x]^2])*
    EllipticF[ArcSin[Rt[d/c,2]*(-1)^(1/4)*Sqrt[c*Sin[a+b*x]]/Sqrt[d*Cos[a+b*x]]],-1] /;
FreeQ[{a,b,c,d},x]


Int[Sqrt[c_.*sin[a_.+b_.*x_]]*Sqrt[d_.*cos[a_.+b_.*x_]],x_Symbol] :=
  d*(c*Sin[a + b*x])^(3/2)/(b*c*Sqrt[d*Cos[a + b*x]]) + 
  (-1)^(1/4)*d*Sec[a + b*x]/(b*Sqrt[d/c]*Sqrt[Sec[a + b*x]^2])*
     EllipticE[ArcSin[Sqrt[d/c]*(-1)^(1/4)*Sqrt[c*Sin[a + b*x]]/Sqrt[d*Cos[a + b*x]]], -1] - 
  (-1)^(1/4)*d*Sec[a + b*x]/(b*Sqrt[d/c]*Sqrt[Sec[a + b*x]^2])*
     EllipticF[ArcSin[Sqrt[d/c]*(-1)^(1/4)*Sqrt[c*Sin[a + b*x]]/Sqrt[d*Cos[a + b*x]]], -1] /;
FreeQ[{a,b,c,d},x]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  Module[{k=Denominator[m]},
  k*c*d/b*Subst[Int[x^(k*(m+1)-1)/(c^2+d^2*x^(2*k)),x],x,(c*Sin[a+b*x])^(1/k)/(d*Cos[a+b*x])^(1/k)]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && RationalQ[m] && 0<m<1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  Module[{k=Denominator[m]},
  -k*c*d/b*Subst[Int[x^(k*(n+1)-1)/(d^2+c^2*x^(2*k)),x],x,(d*Cos[a+b*x])^(1/k)/(c*Sin[a+b*x])^(1/k)]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && RationalQ[m] && -1<m<0


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Sin[a+b*x])^(m+1)*(d*Cos[a+b*x])^(n+1)/(b*c*d*(n+1)*(Sin[a+b*x]^2)^((m+1)/2))*
    Hypergeometric2F1[-(m-1)/2,(n+1)/2,(n+3)/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c,d,m,n},x] && Not[PositiveIntegerQ[(m+1)/2]] && Not[IntegerQ[(n-1)/2]]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Csc[a+b*x])^m*(d*Sec[a+b*x])^n/Tan[a+b*x]^n*Int[Tan[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && (Not[IntegerQ[m]] || Not[IntegerQ[n]]) && ZeroQ[m+n]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  Sin[a+b*x]^m*Cos[a+b*x]^n*(c*Csc[a+b*x])^m*(d*Sec[a+b*x])^n*Int[1/(Sin[a+b*x]^m*Cos[a+b*x]^n),x] /;
FreeQ[{a,b,c,d,m,n},x] && (Not[IntegerQ[m]] || Not[IntegerQ[n]])


Int[(c_.*sin[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  (d*Cos[a+b*x])^n*(d*Sec[a+b*x])^n*Int[(c*Sin[a+b*x])^m/(d*Cos[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.*cos[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  (d*Sin[a+b*x])^n*(d*Csc[a+b*x])^n*Int[(c*Cos[a+b*x])^m/(d*Sin[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol]:=
  -d*(c*Sin[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*m) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m+n-1]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Cos[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*m) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m+n-1]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Sin[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*m) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m-n-1]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*m) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m-n-1]


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Sec[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*m) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m+n+1]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Csc[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*m) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m+n+1]


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Sec[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*m) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m-n+1]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Csc[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*m) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m-n+1]


Int[sin[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_.,x_Symbol] :=
  -1/b*Subst[Int[(1-x^2)^((m+n-1)/2)/x^n,x],x,Cos[a+b*x]] /;
FreeQ[{a,b},x] && IntegersQ[m,n,(m+n-1)/2]


Int[cos[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[(1-x^2)^((m+n-1)/2)/x^n,x],x,Sin[a+b*x]] /;
FreeQ[{a,b},x] && IntegersQ[m,n,(m+n-1)/2]


Int[sin[a_.+b_.*x_]*tan[a_.+b_.*x_],x_Symbol] :=
  -Sin[a+b*x]/b + Int[Sec[a+b*x],x] /;
FreeQ[{a,b},x]


Int[cos[a_.+b_.*x_]*cot[a_.+b_.*x_],x_Symbol] :=
  Cos[a+b*x]/b + Int[Csc[a+b*x],x] /;
FreeQ[{a,b},x]


Int[(c_.*sec[a_.+b_.*x_])^m_.*tan[a_.+b_.*x_],x_Symbol] :=
  (c*Sec[a+b*x])^m/(b*m) /;
FreeQ[{a,b,c,m},x]


Int[(c_.*csc[a_.+b_.*x_])^m_.*cot[a_.+b_.*x_],x_Symbol] :=
  -(c*Csc[a+b*x])^m/(b*m) /;
FreeQ[{a,b,c,m},x]


Int[sec[a_.+b_.*x_]^2*(d_.*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
  (d*Tan[a+b*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,d,n},x] && NonzeroQ[n+1]


Int[csc[a_.+b_.*x_]^2*(d_.*cot[a_.+b_.*x_])^n_.,x_Symbol] :=
  -(d*Cot[a+b*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,d,n},x] && NonzeroQ[n+1]


Int[sec[a_.+b_.*x_]^m_*(d_.*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
  1/b*Subst[Int[(d*x)^n*(1+x^2)^((m-2)/2),x],x,Tan[a+b*x]] /;
FreeQ[{a,b,d,n},x] && EvenQ[m] && Not[OddQ[n] && 0<n<m-1]


Int[csc[a_.+b_.*x_]^m_*(d_.*cot[a_.+b_.*x_])^n_.,x_Symbol] :=
  -1/b*Subst[Int[(d*x)^n*(1+x^2)^((m-2)/2),x],x,Cot[a+b*x]] /;
FreeQ[{a,b,d,n},x] && EvenQ[m] && Not[OddQ[n] && 0<n<m-1]


Int[(c_.*sec[a_.+b_.*x_])^m_.*tan[a_.+b_.*x_]^n_.,x_Symbol] :=
  c/b*Subst[Int[(c*x)^(m-1)*(-1+x^2)^((n-1)/2),x],x,Sec[a+b*x]] /;
FreeQ[{a,b,c,m},x] && OddQ[n] && Not[EvenQ[m] && 0<m<=n+1]


Int[(c_.*csc[a_.+b_.*x_])^m_.*cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  -c/b*Subst[Int[(c*x)^(m-1)*(-1+x^2)^((n-1)/2),x],x,Csc[a+b*x]] /;
FreeQ[{a,b,c,m},x] && OddQ[n] && Not[EvenQ[m] && 0<m<=n+1]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*m) - 
  c^2*(n+1)/(d^2*m)*Int[(c*Sin[a+b*x])^(m-2)*(d*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && n<-1


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Cos[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*m) - 
  c^2*(n+1)/(d^2*m)*Int[(c*Cos[a+b*x])^(m-2)*(d*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && n<-1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Sin[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*m) + 
  c^2*d^2*(n-1)/m*Int[(c*Sin[a+b*x])^(m-2)*(d*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && n>1


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Cos[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*m) + 
  c^2*d^2*(n-1)/m*Int[(c*Cos[a+b*x])^(m-2)*(d*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && n>1


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  c^2*(c*Sec[a+b*x])^(m-2)*(d*Tan[a+b*x])^(n+1)/(b*d*(n+1)) - 
  c^2*(m-2)/(d^2*(n+1))*Int[(c*Sec[a+b*x])^(m-2)*(d*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && m!=2 && n<-1


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -c^2*(c*Csc[a+b*x])^(m-2)*(d*Cot[a+b*x])^(n+1)/(b*d*(n+1)) - 
  c^2*(m-2)/(d^2*(n+1))*Int[(c*Csc[a+b*x])^(m-2)*(d*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && m!=2 && n<-1


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -c^2*d*(c*Sec[a+b*x])^(m-2)*(d*Cot[a+b*x])^(n-1)/(b*(n-1)) + 
  c^2*d^2*(m-2)/(n-1)*Int[(c*Sec[a+b*x])^(m-2)*(d*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && m!=2 && n>1


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  c^2*d*(c*Csc[a+b*x])^(m-2)*(d*Tan[a+b*x])^(n-1)/(b*(n-1)) + 
  c^2*d^2*(m-2)/(n-1)*Int[(c*Csc[a+b*x])^(m-2)*(d*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m>1 && m!=2 && n>1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_.,x_Symbol]:=
  -d*(c*Sin[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*m) + 
  c^2*(m+n-1)/m*Int[(c*Sin[a+b*x])^(m-2)*(d*Tan[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && RationalQ[n]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_.,x_Symbol] :=
  d*(c*Cos[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*m) + 
  c^2*(m+n-1)/m*Int[(c*Cos[a+b*x])^(m-2)*(d*Cot[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && RationalQ[n]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Sin[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*m) + 
  (c^2*(m-n-1))/m*Int[(c*Sin[a+b*x])^(m-2)*(d*Cot[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && NonzeroQ[m-n-1] && RationalQ[n]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*m) + 
  (c^2*(m-n-1))/m*Int[(c*Cos[a+b*x])^(m-2)*(d*Tan[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && NonzeroQ[m-n-1] && RationalQ[n]


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  c^2*(c*Sec[a+b*x])^(m-2)*(d*Tan[a+b*x])^(n+1)/(b*d*(m+n-1)) + 
  c^2*(m-2)/(m+n-1)*Int[(c*Sec[a+b*x])^(m-2)*(d*Tan[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && m!=2 && NonzeroQ[m+n-1] && RationalQ[n]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -c^2*(c*Csc[a+b*x])^(m-2)*(d*Cot[a+b*x])^(n+1)/(b*d*(m+n-1)) + 
  c^2*(m-2)/(m+n-1)*Int[(c*Csc[a+b*x])^(m-2)*(d*Cot[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && m!=2 && NonzeroQ[m+n-1] && RationalQ[n]


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  c^2*d*(c*Sec[a+b*x])^(m-2)*(d*Cot[a+b*x])^(n-1)/(b*(m-n-1)) + 
  c^2*(m-2)/(m-n-1)*Int[(c*Sec[a+b*x])^(m-2)*(d*Cot[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && m!=2 && NonzeroQ[m-n-1] && RationalQ[n]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  -c^2*d*(c*Csc[a+b*x])^(m-2)*(d*Tan[a+b*x])^(n-1)/(b*(m-n-1)) + 
  c^2*(m-2)/(m-n-1)*Int[(c*Csc[a+b*x])^(m-2)*(d*Tan[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m>1 && m!=2 && NonzeroQ[m-n-1] && RationalQ[n]


Int[(d_.*tan[a_.+b_.*x_])^n_*csc[a_.+b_.*x_]^2,x_Symbol] :=
  d*(d*Tan[a+b*x])^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,d,n},x] && NonzeroQ[n-1]


Int[(d_.*cot[a_.+b_.*x_])^n_*sec[a_.+b_.*x_]^2,x_Symbol] :=
  -d*(d*Cot[a+b*x])^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,d,n},x] && NonzeroQ[n-1]


Int[(d_.*cot[a_.+b_.*x_])^n_*csc[a_.+b_.*x_]^2,x_Symbol] :=
  -(d*Cot[a+b*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,d,n},x] && NonzeroQ[n+1]


Int[(d_.*tan[a_.+b_.*x_])^n_*sec[a_.+b_.*x_]^2,x_Symbol] :=
  (d*Tan[a+b*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,d,n},x] && NonzeroQ[n+1]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Sin[a+b*x])^(m+2)*(d*Tan[a+b*x])^(n-1)/(b*c^2*(n-1)) - 
  d^2*(m+2)/(c^2*(n-1))*Int[(c*Sin[a+b*x])^(m+2)*(d*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && m!=-2 && n>1


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Cos[a+b*x])^(m+2)*(d*Cot[a+b*x])^(n-1)/(b*c^2*(n-1)) - 
  d^2*(m+2)/(c^2*(n-1))*Int[(c*Cos[a+b*x])^(m+2)*(d*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && m!=-2 && n>1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Sin[a+b*x])^(m+2)*(d*Cot[a+b*x])^(n+1)/(b*c^2*d*(n+1)) + 
  (m+2)/(c^2*d^2*(n+1))*Int[(c*Sin[a+b*x])^(m+2)*(d*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && m!=-2 && n<-1


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^(m+2)*(d*Tan[a+b*x])^(n+1)/(b*c^2*d*(n+1)) + 
  (m+2)/(c^2*d^2*(n+1))*Int[(c*Cos[a+b*x])^(m+2)*(d*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && m!=-2 && n<-1


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Sec[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*m) - 
  d^2*(n-1)/(c^2*m)*Int[(c*Sec[a+b*x])^(m+2)*(d*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && n>1


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Csc[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*m) - 
  d^2*(n-1)/(c^2*m)*Int[(c*Csc[a+b*x])^(m+2)*(d*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && n>1


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sec[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*m) + 
  (n+1)/(c^2*d^2*m)*Int[(c*Sec[a+b*x])^(m+2)*(d*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && n<-1


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Csc[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*m) + 
  (n+1)/(c^2*d^2*m)*Int[(c*Csc[a+b*x])^(m+2)*(d*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && m<-1 && n<-1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_.,x_Symbol]:=
  d*(c*Sin[a+b*x])^(m+2)*(d*Tan[a+b*x])^(n-1)/(b*c^2*(m+n+1)) + 
  (m+2)/(c^2*(m+n+1))*Int[(c*Sin[a+b*x])^(m+2)*(d*Tan[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && m!=-2 && NonzeroQ[m+n+1] && RationalQ[n]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_.,x_Symbol] :=
  -d*(c*Cos[a+b*x])^(m+2)*(d*Cot[a+b*x])^(n-1)/(b*c^2*(m+n+1)) + 
  (m+2)/(c^2*(m+n+1))*Int[(c*Cos[a+b*x])^(m+2)*(d*Cot[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && m!=-2 && NonzeroQ[m+n+1] && RationalQ[n]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^(m+2)*(d*Cot[a+b*x])^(n+1)/(b*c^2*d*(m-n+1)) + 
  (m+2)/(c^2*(m-n+1))*Int[(c*Sin[a+b*x])^(m+2)*(d*Cot[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && m!=-2 && NonzeroQ[m-n+1] && RationalQ[n]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Cos[a+b*x])^(m+2)*(d*Tan[a+b*x])^(n+1)/(b*c^2*d*(m-n+1)) + 
  (m+2)/(c^2*(m-n+1))*Int[(c*Cos[a+b*x])^(m+2)*(d*Tan[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && m!=-2 && NonzeroQ[m-n+1] && RationalQ[n]


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Sec[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*m) + 
  (m+n+1)/(c^2*m)*Int[(c*Sec[a+b*x])^(m+2)*(d*Tan[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+1] && RationalQ[n]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Csc[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*m) + 
  (m+n+1)/(c^2*m)*Int[(c*Csc[a+b*x])^(m+2)*(d*Cot[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+1] && RationalQ[n]


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Sec[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*m) + 
  (m-n+1)/(c^2*m)*Int[(c*Sec[a+b*x])^(m+2)*(d*Cot[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m-n+1] && RationalQ[n]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Csc[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*m) + 
  (m-n+1)/(c^2*m)*Int[(c*Csc[a+b*x])^(m+2)*(d*Tan[a+b*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m-n+1] && RationalQ[n]


Int[(c_.*sin[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Sin[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*(n-1)) - 
  d^2*(m+n-1)/(n-1)*Int[(c*Sin[a+b*x])^m*(d*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1] && RationalQ[m]


Int[(c_.*cos[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Cos[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*(n-1)) - 
  d^2*(m+n-1)/(n-1)*Int[(c*Cos[a+b*x])^m*(d*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1] && RationalQ[m]


Int[(c_.*sin[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol]:=
  d*(c*Sin[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*(m-n+1)) + 
  d^2*(n-1)/(m-n+1)*Int[(c*Sin[a+b*x])^m*(d*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m-n+1] && RationalQ[m]


Int[(c_.*cos[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol]:=
  -d*(c*Cos[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*(m-n+1)) + 
  d^2*(n-1)/(m-n+1)*Int[(c*Cos[a+b*x])^m*(d*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m-n+1] && RationalQ[m]


Int[(c_.*sec[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Sec[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*(m+n-1)) - 
  d^2*(n-1)/(m+n-1)*Int[(c*Sec[a+b*x])^m*(d*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1] && RationalQ[m]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Csc[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*(m+n-1)) - 
  d^2*(n-1)/(m+n-1)*Int[(c*Csc[a+b*x])^m*(d*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1] && RationalQ[m]


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -d*(c*Sec[a+b*x])^m*(d*Cot[a+b*x])^(n-1)/(b*(n-1)) + 
  d^2*(m-n+1)/(n-1)*Int[(c*Sec[a+b*x])^m*(d*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m-n+1] && RationalQ[m]


Int[(c_.*csc[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  d*(c*Csc[a+b*x])^m*(d*Tan[a+b*x])^(n-1)/(b*(n-1)) + 
  d^2*(m-n+1)/(n-1)*Int[(c*Csc[a+b*x])^m*(d*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n>1 && NonzeroQ[m-n+1] && RationalQ[m]


Int[(c_.*sin[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol]:=
  (c*Sin[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*(m+n+1)) - 
  (n+1)/(d^2*(m+n+1))*Int[(c*Sin[a+b*x])^m*(d*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1] && RationalQ[m]


Int[(c_.*cos[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Cos[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*(m+n+1)) - 
  (n+1)/(d^2*(m+n+1))*Int[(c*Cos[a+b*x])^m*(d*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1] && RationalQ[m]


Int[(c_.*sin[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Sin[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*(n+1)) + 
  (m-n-1)/(d^2*(n+1))*Int[(c*Sin[a+b*x])^m*(d*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m-n-1] && RationalQ[m]


Int[(c_.*cos[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*(n+1)) + 
  (m-n-1)/(d^2*(n+1))*Int[(c*Cos[a+b*x])^m*(d*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m-n-1] && RationalQ[m]


Int[(c_.*sec[a_.+b_.*x_])^m_*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sec[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*(n+1)) - 
  (m+n+1)/(d^2*(n+1))*Int[(c*Sec[a+b*x])^m*(d*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1] && RationalQ[m]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Csc[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*(n+1)) - 
  (m+n+1)/(d^2*(n+1))*Int[(c*Csc[a+b*x])^m*(d*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1] && RationalQ[m]


Int[(c_.*sec[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sec[a+b*x])^m*(d*Cot[a+b*x])^(n+1)/(b*d*(m-n-1)) + 
  (n+1)/(d^2*(m-n-1))*Int[(c*Sec[a+b*x])^m*(d*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m-n-1] && RationalQ[m]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Csc[a+b*x])^m*(d*Tan[a+b*x])^(n+1)/(b*d*(m-n-1)) + 
  (n+1)/(d^2*(m-n-1))*Int[(c*Csc[a+b*x])^m*(d*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c,d,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m-n-1] && RationalQ[m]


Int[(c_.*sin[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Sin[a+b*x])^m*(d*Tan[a+b*x])^n*Cos[a+b*x]^n/Sin[a+b*x]^(m+n)*Int[Sin[a+b*x]^(m+n)/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(c_.*cos[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cos[a+b*x])^m*(d*Cot[a+b*x])^n*Sin[a+b*x]^n/Cos[a+b*x]^(m+n)*Int[Cos[a+b*x]^(m+n)/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(c_.*sin[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^m*(d*Cot[a+b*x])^n/(Sin[a+b*x]^(m-n)*Cos[a+b*x]^n)*Int[Sin[a+b*x]^(m-n)*Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.*cos[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^m*(d*Tan[a+b*x])^n/(Sin[a+b*x]^n*Cos[a+b*x]^(m-n))*Int[Sin[a+b*x]^n*Cos[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.*sec[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sec[a+b*x])^m*(d*Tan[a+b*x])^n*Csc[a+b*x]^n/Sec[a+b*x]^(m+n)*Int[Sec[a+b*x]^(m+n)/Csc[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Csc[a+b*x])^m*(d*Cot[a+b*x])^n*Sec[a+b*x]^n/Csc[a+b*x]^(m+n)*Int[Csc[a+b*x]^(m+n)/Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.*sec[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sec[a+b*x])^m*(d*Cot[a+b*x])^n/(Csc[a+b*x]^n*Sec[a+b*x]^(m-n))*Int[Csc[a+b*x]^n*Sec[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(c_.*csc[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Csc[a+b*x])^m*(d*Tan[a+b*x])^n/(Csc[a+b*x]^(m-n)*Sec[a+b*x]^n)*Int[Csc[a+b*x]^(m-n)*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[sin[a_.+b_.*x_]^m_.*(d_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  d^m*Int[(d*Csc[a+b*x])^(n-m),x] /;
FreeQ[{a,b,d,n},x] && IntegerQ[m]


Int[cos[a_.+b_.*x_]^m_.*(d_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  d^m*Int[(d*Sec[a+b*x])^(n-m),x] /;
FreeQ[{a,b,d,n},x] && IntegerQ[m]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^n*(d*Csc[a+b*x])^n*Int[(c*Sin[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[m]]


Int[(c_.*cos[a_.+b_.*x_])^m_*(d_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^n*(d*Sec[a+b*x])^n*Int[(c*Cos[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[m]]


Int[(c_.*tan[a_.+b_.*x_])^m_.*(d_.*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Tan[a+b*x])^n*(d*Cot[a+b*x])^n*Int[(c*Tan[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[sin[a_.+b_.*x_]*sin[c_.+d_.*x_],x_Symbol] :=
  Sin[a-c+(b-d)*x]/(2*(b-d)) - Sin[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b^2-d^2]


Int[cos[a_.+b_.*x_]*cos[c_.+d_.*x_],x_Symbol] :=
  Sin[a-c+(b-d)*x]/(2*(b-d)) + Sin[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b^2-d^2]


Int[sin[a_.+b_.*x_]*cos[c_.+d_.*x_],x_Symbol] :=
  -Cos[a-c+(b-d)*x]/(2*(b-d)) - Cos[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b^2-d^2]


Int[cos[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  1/2*Int[(g*Sin[c+d*x])^p,x] + 
  1/2*Int[Cos[c+d*x]*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && PositiveIntegerQ[p/2]


Int[sin[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  1/2*Int[(g*Sin[c+d*x])^p,x] - 
  1/2*Int[Cos[c+d*x]*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && PositiveIntegerQ[p/2]


Int[(e_.*cos[a_.+b_.*x_])^m_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
  2^p/e^p*Int[(e*Cos[a+b*x])^(m+p)*Sin[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && IntegerQ[p]


Int[(f_.*sin[a_.+b_.*x_])^n_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
  2^p/f^p*Int[Cos[a+b*x]^p*(f*Sin[a+b*x])^(n+p),x] /;
FreeQ[{a,b,c,d,f,n},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && IntegerQ[p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) /;
FreeQ[{a,b,c,d,e,g,m,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && ZeroQ[m+p-1]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) /;
FreeQ[{a,b,c,d,e,g,m,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && ZeroQ[m+p-1]


Int[(e_.*cos[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(b*g*m) /;
FreeQ[{a,b,c,d,e,g,m,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && ZeroQ[m+2*p+2]


Int[(e_.*sin[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(b*g*m) /;
FreeQ[{a,b,c,d,e,g,m,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && ZeroQ[m+2*p+2]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  e^4*(m+p-1)/(4*g^2*(p+1))*Int[(e*Cos[a+b*x])^(m-4)*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>2 && p<-1 && 
  (m>3 || p==-3/2) && IntegersQ[2*m,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  e^4*(m+p-1)/(4*g^2*(p+1))*Int[(e*Sin[a+b*x])^(m-4)*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>2 && p<-1 && 
  (m>3 || p==-3/2) && IntegersQ[2*m,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  e^2*(m+2*p+2)/(4*g^2*(p+1))*Int[(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>1 && p<-1 && 
  NonzeroQ[m+2*p+2] && (p<-2 || m==2) && IntegersQ[2*m,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  e^2*(m+2*p+2)/(4*g^2*(p+1))*Int[(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>1 && p<-1 && 
  NonzeroQ[m+2*p+2] && (p<-2 || m==2) && IntegersQ[2*m,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+2*p)) + 
  e^2*(m+p-1)/(m+2*p)*Int[(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,g,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m>1 && NonzeroQ[m+2*p] &&
  IntegersQ[2*m,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+2*p)) + 
  e^2*(m+p-1)/(m+2*p)*Int[(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,g,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m>1 && NonzeroQ[m+2*p] &&
  IntegersQ[2*m,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+p+1)) + 
  (m+2*p+2)/(e^2*(m+p+1))*Int[(e*Cos[a+b*x])^(m+2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,g,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m<-1 && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+p+1] && IntegersQ[2*m,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+p+1)) + 
  (m+2*p+2)/(e^2*(m+p+1))*Int[(e*Sin[a+b*x])^(m+2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,g,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m<-1 && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+p+1] && IntegersQ[2*m,2*p]


Int[cos[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  2*Sin[a+b*x]*(g*Sin[c+d*x])^p/(d*(2*p+1)) + 2*p*g/(2*p+1)*Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[p] && p>0 && IntegerQ[2*p]


Int[sin[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -2*Cos[a+b*x]*(g*Sin[c+d*x])^p/(d*(2*p+1)) + 2*p*g/(2*p+1)*Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[p] && p>0 && IntegerQ[2*p]


Int[cos[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Cos[a+b*x]*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  (2*p+3)/(2*g*(p+1))*Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[p] && p<-1 && IntegerQ[2*p]


Int[sin[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -Sin[a+b*x]*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  (2*p+3)/(2*g*(p+1))*Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[p] && p<-1 && IntegerQ[2*p]


Int[cos[a_.+b_.*x_]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  -ArcSin[Cos[a+b*x]-Sin[a+b*x]]/d + Log[Cos[a+b*x]+Sin[a+b*x]+Sqrt[Sin[c+d*x]]]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2]


Int[sin[a_.+b_.*x_]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  -ArcSin[Cos[a+b*x]-Sin[a+b*x]]/d - Log[Cos[a+b*x]+Sin[a+b*x]+Sqrt[Sin[c+d*x]]]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2]


Int[(g_.*sin[c_.+d_.*x_])^p_/cos[a_.+b_.*x_],x_Symbol] :=
  2*g*Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,g,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && IntegerQ[2*p]


Int[(g_.*sin[c_.+d_.*x_])^p_/sin[a_.+b_.*x_],x_Symbol] :=
  2*g*Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,g,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && IntegerQ[2*p]


(* Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*Sin[a+b*x]*(g*Sin[c+d*x])^p/(b*e*(m+p+1)*(Sin[a+b*x]^2)^((p+1)/2))*
    Hypergeometric2F1[-(p-1)/2,(m+p+1)/2,(m+p+3)/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c,d,e,g,m,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && Not[IntegerQ[m+p]] *)


(* Int[(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -Cos[a+b*x]*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(p+1)*(Sin[a+b*x]^2)^((n+p+1)/2))*
    Hypergeometric2F1[-(n+p-1)/2,(p+1)/2,(p+3)/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c,d,f,g,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && Not[IntegerQ[n+p]] *)


Int[(e_.*cos[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (g*Sin[c+d*x])^p/((e*Cos[a+b*x])^p*Sin[a+b*x]^p)*Int[(e*Cos[a+b*x])^(m+p)*Sin[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,e,g,m,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]]


Int[(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (g*Sin[c+d*x])^p/(Cos[a+b*x]^p*(f*Sin[a+b*x])^p)*Int[Cos[a+b*x]^p*(f*Sin[a+b*x])^(n+p),x] /;
FreeQ[{a,b,c,d,f,g,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]]


Int[cos[a_.+b_.*x_]^2*sin[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  1/4*Int[(g*Sin[c+d*x])^p,x] - 
  1/4*Int[Cos[c+d*x]^2*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && PositiveIntegerQ[p/2]


Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
  2^p/(e^p*f^p)*Int[(e*Cos[a+b*x])^(m+p)*(f*Sin[a+b*x])^(n+p),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && IntegerQ[p]


Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && ZeroQ[m+p+1]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && ZeroQ[m+p+1]


Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && ZeroQ[m+n+2*p+2] && NonzeroQ[m+p+1]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e^2*(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) + 
  e^4*(m+p-1)/(4*g^2*(n+p+1))*Int[(e*Cos[a+b*x])^(m-4)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>3 && p<-1 && 
  NonzeroQ[n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e^2*(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) + 
  e^4*(m+p-1)/(4*g^2*(n+p+1))*Int[(e*Sin[a+b*x])^(m-4)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>3 && p<-1 && 
  NonzeroQ[n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Cos[a+b*x])^m*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) + 
  e^2*(m+n+2*p+2)/(4*g^2*(n+p+1))*Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>1 && p<-1 && 
  NonzeroQ[m+n+2*p+2] && NonzeroQ[n+p+1] && IntegersQ[2*m,2*n,2*p] && (p<-2 || m==2 || m==3)


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Sin[a+b*x])^m*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) + 
  e^2*(m+n+2*p+2)/(4*g^2*(n+p+1))*Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>1 && p<-1 && 
  NonzeroQ[m+n+2*p+2] && NonzeroQ[n+p+1] && IntegersQ[2*m,2*n,2*p] && (p<-2 || m==2 || m==3)


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) + 
  e^2*(m+p-1)/(f^2*(n+p+1))*Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^(n+2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n] && m>1 && n<-1 && 
  NonzeroQ[n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) + 
  e^2*(m+p-1)/(f^2*(n+p+1))*Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^(n+2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n] && m>1 && n<-1 && 
  NonzeroQ[n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(m+n+2*p)) + 
  e^2*(m+p-1)/(m+n+2*p)*Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m>1 && NonzeroQ[m+n+2*p] && 
  IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(m+n+2*p)) + 
  e^2*(m+p-1)/(m+n+2*p)*Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m>1 && NonzeroQ[m+n+2*p] && 
  IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -f*(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^p/(b*e*(m+n+2*p)) + 
  2*f*g*(n+p-1)/(e*(m+n+2*p))*Int[(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n,p] && m<-1 && n>0 && p>0 && 
  NonzeroQ[m+n+2*p] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  f*(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^p/(b*e*(m+n+2*p)) + 
  2*f*g*(n+p-1)/(e*(m+n+2*p))*Int[(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n,p] && m<-1 && n>0 && p>0 && 
  NonzeroQ[m+n+2*p] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) + 
  f*(m+n+2*p+2)/(2*e*g*(m+p+1))*Int[(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n,p] && m<-1 && n>0 && p<-1 && 
  NonzeroQ[m+n+2*p+2] && NonzeroQ[m+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) + 
  f*(m+n+2*p+2)/(2*e*g*(m+p+1))*Int[(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n,p] && m<-1 && n>0 && p<-1 && 
  NonzeroQ[m+n+2*p+2] && NonzeroQ[m+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) + 
  (m+n+2*p+2)/(e^2*(m+p+1))*Int[(e*Cos[a+b*x])^(m+2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m<-1 && 
  NonzeroQ[m+n+2*p+2] && NonzeroQ[m+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) + 
  (m+n+2*p+2)/(e^2*(m+p+1))*Int[(e*Sin[a+b*x])^(m+2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m<-1 && 
  NonzeroQ[m+n+2*p+2] && NonzeroQ[m+p+1] && IntegersQ[2*m,2*n,2*p]


(* Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)*(Sin[a+b*x]^2)^((n+p+1)/2))*
    Hypergeometric2F1[-(n+p-1)/2,(m+p+1)/2,(m+p+3)/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]] && Not[IntegerQ[m+p]] && Not[IntegerQ[n+p]] *)


Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (g*Sin[c+d*x])^p/((e*Cos[a+b*x])^p*(f*Sin[a+b*x])^p)*Int[(e*Cos[a+b*x])^(m+p)*(f*Sin[a+b*x])^(n+p),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-2] && Not[IntegerQ[p]]


Int[(e_.*cos[a_.+b_.*x_])^m_.*sin[c_.+d_.*x_],x_Symbol] :=
  -(m+2)*(e*Cos[a+b*x])^(m+1)*Cos[(m+1)*(a+b*x)]/(d*e*(m+1)) /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b*c-a*d] && ZeroQ[d/b-Abs[m+2]]


(* ::Section:: *)
(*Sine Function Rules*)


(* ::Subsection::Closed:: *)
(*1 (c sin)^n*)


If[ShowSteps,

Int[u_,x_Symbol] :=
  Int[DeactivateTrig[u,x],x] /;
SimplifyFlag && FunctionOfTrigOfLinearQ[u,x],

Int[u_,x_Symbol] :=
  Int[DeactivateTrig[u,x],x] /;
FunctionOfTrigOfLinearQ[u,x]]


Int[sin[a_.+b_.*x_],x_Symbol] :=
  -Cos[a+b*x]/b /;
FreeQ[{a,b},x]


Int[cos[a_.+b_.*x_],x_Symbol] :=
  Sin[a+b*x]/b /;
FreeQ[{a,b},x]


Int[sin[a_.+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[Expand[(1-x^2)^((n-1)/2),x],x],x,Cos[a+b*x]] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && OddQ[n]


Int[cos[a_.+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[Expand[(1-x^2)^((n-1)/2),x],x],x,Sin[a+b*x]] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && OddQ[n]


Int[sin[a_.+b_.*x_]^2,x_Symbol] :=
  x/2 - Cos[a+b*x]*Sin[a+b*x]/(2*b) /;
FreeQ[{a,b},x]


Int[cos[a_.+b_.*x_]^2,x_Symbol] :=
  x/2 + Cos[a+b*x]*Sin[a+b*x]/(2*b) /;
FreeQ[{a,b},x]


Int[(c_.*sin[a_.+b_.*x_])^n_,x_Symbol] :=
(* -Cot[a+b*x]*(c*Sin[a+b*x])^n/(b*n) + *)
  -c*Cos[a+b*x]*(c*Sin[a+b*x])^(n-1)/(b*n) + 
  c^2*(n-1)/n*Int[(c*Sin[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1 && Not[OddQ[n]]


Int[(c_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
(* Tan[a+b*x]*(c*Cos[a+b*x])^n/(b*n) + *)
  c*Sin[a+b*x]*(c*Cos[a+b*x])^(n-1)/(b*n) + 
  c^2*(n-1)/n*Int[(c*Cos[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1 && Not[OddQ[n]]


(* Int[1/sin[a_.+b_.*x_],x_Symbol] :=
  Int[Csc[a+b*x],x] /;
FreeQ[{a,b},x] *)


(* Int[1/cos[a_.+b_.*x_],x_Symbol] :=
  Int[Sec[a+b*x],x] /;
FreeQ[{a,b},x] *)


Int[(c_.*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]*(c*Sin[a+b*x])^(n+1)/(b*c*(n+1)) + 
  (n+2)/(c^2*(n+1))*Int[(c*Sin[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  -Sin[a+b*x]*(c*Cos[a+b*x])^(n+1)/(b*c*(n+1)) + 
  (n+2)/(c^2*(n+1))*Int[(c*Cos[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[Sqrt[sin[a_.+b_.*x_]],x_Symbol] :=
  -2*EllipticE[Pi/4-(a+b*x)/2,2]/b /;
FreeQ[{a,b},x]


Int[Sqrt[cos[a_.+b_.*x_]],x_Symbol] :=
  2*EllipticE[(a+b*x)/2,2]/b /;
FreeQ[{a,b},x]


Int[1/Sqrt[sin[a_.+b_.*x_]],x_Symbol] :=
  -2*EllipticF[Pi/4-(a+b*x)/2,2]/b /;
FreeQ[{a,b},x]


Int[1/Sqrt[cos[a_.+b_.*x_]],x_Symbol] :=
  2*EllipticF[(a+b*x)/2,2]/b /;
FreeQ[{a,b},x]


Int[(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^n/Sin[a+b*x]^n*Int[Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && ZeroQ[n^2-1/4]


Int[(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^n/Cos[a+b*x]^n*Int[Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && ZeroQ[n^2-1/4]


Int[(c_.*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*Cos[a+b*x]*(c*Sin[a+b*x])^(n-1)/(b*(Sin[a+b*x]^2)^((n-1)/2))*
    Hypergeometric2F1[1/2,(1-n)/2,3/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[2*n]] && RationalQ[n] && n>0


Int[(c_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  c*Sin[a+b*x]*(c*Cos[a+b*x])^(n-1)/(b*(Cos[a+b*x]^2)^((n-1)/2))*
    Hypergeometric2F1[1/2,(1-n)/2,3/2,Sin[a+b*x]^2] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[2*n]] && RationalQ[n] && n>0


Int[(c_.*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  -Cos[a+b*x]*(c*Sin[a+b*x])^(n+1)/(b*c*(Sin[a+b*x]^2)^((n+1)/2))*
    Hypergeometric2F1[1/2,(1-n)/2,3/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[2*n]] && Not[RationalQ[n] && n>0]


Int[(c_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  Sin[a+b*x]*(c*Cos[a+b*x])^(n+1)/(b*c*(Cos[a+b*x]^2)^((n+1)/2))*
    Hypergeometric2F1[1/2,(1-n)/2,3/2,Sin[a+b*x]^2] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[2*n]] && Not[RationalQ[n] && n>0]


(* ::Subsection::Closed:: *)
(*2 (a+b sin)^n*)


Int[(a_+b_.*sin[c_.+d_.*x_])^2,x_Symbol] :=
  (2*a^2+b^2)*x/2 - b^2*Cos[c+d*x]*Sin[c+d*x]/(2*d) + 2*a*b*Int[Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*cos[c_.+d_.*x_])^2,x_Symbol] :=
  (2*a^2+b^2)*x/2 + b^2*Sin[c+d*x]*Cos[c+d*x]/(2*d) + 2*a*b*Int[Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*b*Cos[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*b*Sin[c+d*x]/(d*Sqrt[a+b*Cos[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) +
  a*(2*n-1)/n*Int[(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n-1)/(d*n) +
  a*(2*n-1)/n*Int[(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]/(d*(b+a*Sin[c+d*x])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Sin[c+d*x]/(d*(b+a*Cos[c+d*x])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2/d*Subst[Int[1/(2*a-x^2),x],x,b*Cos[c+d*x]/Sqrt[a+b*Sin[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2/d*Subst[Int[1/(2*a-x^2),x],x,b*Sin[c+d*x]/Sqrt[a+b*Cos[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(a*d*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Sqrt[2]*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(b*d*(2*n+1)*Sqrt[(a-b*Sin[c+d*x])/a])*
    Hypergeometric2F1[1/2,n+1/2,n+3/2,(a+b*Sin[c+d*x])/(2*a)] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sqrt[2]*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(b*d*(2*n+1)*Sqrt[(a-b*Cos[c+d*x])/a])*
    Hypergeometric2F1[1/2,n+1/2,n+3/2,(a+b*Cos[c+d*x])/(2*a)] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*Sqrt[a+b]/d*EllipticE[Pi/4-(c+d*x)/2,2*b/(a+b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*Sqrt[a+b]/d*EllipticE[(c+d*x)/2,2*b/(a+b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  2*Sqrt[a-b]/d*EllipticE[Pi/4+(c+d*x)/2,-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a-b]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*Sqrt[a-b]/d*EllipticE[Pi/2+(c+d*x)/2,-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a-b]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[a+b*Sin[c+d*x]]/Sqrt[(a+b*Sin[c+d*x])/(a+b)]*Int[Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[a+b*Cos[c+d*x]]/Sqrt[(a+b*Cos[c+d*x])/(a+b)]*Int[Sqrt[a/(a+b)+b/(a+b)*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[(a+b*Sin[c+d*x])^(n-2)*Simp[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Sin[c+d*x],x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[(a+b*Cos[c+d*x])^(n-2)*Simp[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Cos[c+d*x],x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Module[{e=FreeFactors[Tan[(c+d*x)/2],x]},
  2*e/d*Subst[Int[1/(a+2*b*e*x+a*e^2*x^2),x],x,Tan[(c+d*x)/2]/e]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Module[{e=FreeFactors[Tan[(c+d*x)/2],x]},
  2*e/d*Subst[Int[1/(a+b+(a-b)*e^2*x^2),x],x,Tan[(c+d*x)/2]/e]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2/(d*Sqrt[a+b])*EllipticF[Pi/4-(c+d*x)/2,2*b/(a+b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]


Int[1/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2/(d*Sqrt[a+b])*EllipticF[(c+d*x)/2,2*b/(a+b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  2/(d*Sqrt[a-b])*EllipticF[Pi/4+(c+d*x)/2,-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a-b]


Int[1/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2/(d*Sqrt[a-b])*EllipticF[Pi/2+(c+d*x)/2,-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a-b]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[(a+b*Sin[c+d*x])/(a+b)]/Sqrt[a+b*Sin[c+d*x]]*Int[1/Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[1/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[(a+b*Cos[c+d*x])/(a+b)]/Sqrt[a+b*Cos[c+d*x]]*Int[1/Sqrt[a/(a+b)+b/(a+b)*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*Int[(a+b*Sin[c+d*x])^(n+1)*Simp[a*(n+1)-b*(n+2)*Sin[c+d*x],x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*Int[(a+b*Cos[c+d*x])^(n+1)*Simp[a*(n+1)-b*(n+2)*Cos[c+d*x],x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
 (a+b*Sin[c+d*x])^(n+1)*Sqrt[b*(1-Sin[c+d*x])/(a+b)]*Sqrt[-b*(1+Sin[c+d*x])/(a-b)]/(b*d*(n+1)*Cos[c+d*x])*
   AppellF1[n+1,1/2,1/2,n+2,(a+b*Sin[c+d*x])/(a-b),(a+b*Sin[c+d*x])/(a+b)] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
 -(a+b*Cos[c+d*x])^(n+1)*Sqrt[b*(1-Cos[c+d*x])/(a+b)]*Sqrt[-b*(1+Cos[c+d*x])/(a-b)]/(b*d*(n+1)*Sin[c+d*x])*
   AppellF1[n+1,1/2,1/2,n+2,(a+b*Cos[c+d*x])/(a-b),(a+b*Cos[c+d*x])/(a+b)] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*sin[c_.+d_.*x_]*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[(a+b*Sin[2*c+2*d*x]/2)^n,x] /;
FreeQ[{a,b,c,d,n},x]


(* ::Subsection::Closed:: *)
(*3.1 (a+b sin)^m (c+d sin)^n*)


Int[(a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (2*a*c+b*d)*x/2 - (b*c+a*d)*Cos[e+f*x]/f - b*d*Cos[e+f*x]*Sin[e+f*x]/(2*f) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]


Int[(a_+b_.*cos[e_.+f_.*x_])*(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (2*a*c+b*d)*x/2 + (b*c+a*d)*Sin[e+f*x]/f + b*d*Cos[e+f*x]*Sin[e+f*x]/(2*f) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]


Int[(a_.+b_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b*x/d - (b*c-a*d)/d*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]


Int[(a_.+b_.*cos[e_.+f_.*x_])/(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b*x/d - (b*c-a*d)/d*Int[1/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*a^m*c^m*d*Cos[e+f*x]^(2*m+1)/(f*(2*m+1)*(c+d*Sin[e+f*x])^(m+1/2)) /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*Sqrt[c_+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  -2*a^m*c^m*d*Sin[e+f*x]^(2*m+1)/(f*(2*m+1)*(c+d*Cos[e+f*x])^(m+1/2)) /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -a^m*c^m*d*Cos[e+f*x]^(2*m+1)*(c+d*Sin[e+f*x])^(n-m-1)/(f*(m+n)) + 
  c*(2*n-1)/(m+n)*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m] && PositiveIntegerQ[n-1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  a^m*c^m*d*Sin[e+f*x]^(2*m+1)*(c+d*Cos[e+f*x])^(n-m-1)/(f*(m+n)) + 
  c*(2*n-1)/(m+n)*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m] && PositiveIntegerQ[n-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_./Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*a^(m-1)*b*c^(m-1)*Cos[e+f*x]^(2*m-1)/(f*(2*m-1)*(c+d*Sin[e+f*x])^(m-1/2)) + 
  2*a*Int[(a+b*Sin[e+f*x])^(m-1)/Sqrt[c+d*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_./Sqrt[c_+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  2*a^(m-1)*b*c^(m-1)*Sin[e+f*x]^(2*m-1)/(f*(2*m-1)*(c+d*Cos[e+f*x])^(m-1/2)) + 
  2*a*Int[(a+b*Cos[e+f*x])^(m-1)/Sqrt[c+d*Cos[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*a^(m-1)*b*c^(m-1)*Cos[e+f*x]^(2*m-1)*(c+d*Sin[e+f*x])^(n-m+1)/(f*(2*n+1)) - 
  b*(2*m-1)/(d*(2*n+1))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m] && NegativeIntegerQ[n+1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  2*a^(m-1)*b*c^(m-1)*Sin[e+f*x]^(2*m-1)*(c+d*Cos[e+f*x])^(n-m+1)/(f*(2*n+1)) - 
  b*(2*m-1)/(d*(2*n+1))*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m] && NegativeIntegerQ[n+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^(m-1)*b*c^m*Cos[e+f*x]^(2*m+1)*(c+d*Sin[e+f*x])^(n-m)/(f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && NegativeIntegerQ[m] && NegativeIntegerQ[n-1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -a^(m-1)*b*c^m*Sin[e+f*x]^(2*m+1)*(c+d*Cos[e+f*x])^(n-m)/(f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && NegativeIntegerQ[m] && NegativeIntegerQ[n-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^m*c^m*Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m] && Not[IntegerQ[n] && n^2<m^2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^m*c^m*Int[Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m] && Not[IntegerQ[n] && n^2<m^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && ZeroQ[m+n+1] && NonzeroQ[m+1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(a*f*(2*m+1)) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && ZeroQ[m+n+1] && NonzeroQ[m+1/2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Sin[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && NonzeroQ[n+1/2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  2*b*Sin[e+f*x]*(c+d*Cos[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Cos[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && NonzeroQ[n+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(2*n+1)) - 
  b*(2*m-1)/(d*(2*n+1))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && RationalQ[m,n] && m>1 && n<-1 && 
  Not[IntegerQ[m+n] && 0<-(m+n+1)<=m-1/2] && IntegersQ[2*m,2*n]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  2*b*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^n/(f*(2*n+1)) - 
  b*(2*m-1)/(d*(2*n+1))*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && RationalQ[m,n] && m>1 && n<-1 && 
  Not[IntegerQ[m+n] && 0<-(m+n+1)<=m-1/2] && IntegersQ[2*m,2*n]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(m+n)) + 
  a*(2*m-1)/(m+n)*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m-1/2] && NonzeroQ[m+n] && 
  Not[PositiveIntegerQ[n-1/2] && n<m] && Not[IntegerQ[m+n] && 0<-(m+n+1)<=m-1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^n/(f*(m+n)) + 
  a*(2*m-1)/(m+n)*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m-1/2] && NonzeroQ[m+n] && 
  Not[PositiveIntegerQ[n-1/2] && n<m] && Not[IntegerQ[m+n] && 0<-(m+n+1)<=m-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  Not[RationalQ[n] && m<n<-1] && IntegersQ[2*m,2*n]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(a*f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  Not[RationalQ[n] && m<n<-1] && IntegersQ[2*m,2*n]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && NegativeIntegerQ[Simplify[m+n+1]] && 
  Not[SumSimplerQ[n,1]] && NonzeroQ[m+1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(a*f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && NegativeIntegerQ[Simplify[m+n+1]] && 
  Not[SumSimplerQ[n,1]] && NonzeroQ[m+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^(m+1/2)*c^(m+1/2)*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])*Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  a^(m+1/2)*c^(m+1/2)*Sin[e+f*x]/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]])*Int[Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^m/Cos[e+f*x]^(2*m)*Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[IntegerQ[2*m]] && Not[IntegerQ[n]]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  (a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^m/Sin[e+f*x]^(2*m)*Int[Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[IntegerQ[2*m]] && Not[IntegerQ[n]]


Int[(a_.+b_.*sin[e_.+f_.*x_])^2/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b^2*Cos[e+f*x]/(d*f) + 1/d*Int[Simp[a^2*d-b*(b*c-2*a*d)*Sin[e+f*x],x]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]


Int[(a_.+b_.*cos[e_.+f_.*x_])^2/(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b^2*Sin[e+f*x]/(d*f) + 1/d*Int[Simp[a^2*d-b*(b*c-2*a*d)*Cos[e+f*x],x]/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*Sin[e+f*x]),x] - d/(b*c-a*d)*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]


Int[1/((a_.+b_.*cos[e_.+f_.*x_])*(c_.+d_.*cos[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*Cos[e+f*x]),x] - d/(b*c-a*d)*Int[1/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]


Int[(b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  c*Int[(b*Sin[e+f*x])^m,x] + d/b*Int[(b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{b,c,d,e,f,m},x]


Int[(b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  c*Int[(b*Cos[e+f*x])^m,x] + d/b*Int[(b*Cos[e+f*x])^(m+1),x] /;
FreeQ[{b,c,d,e,f,m},x]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[a*d*m+b*c*(m+1)]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  d*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(f*(m+1)) /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[a*d*m+b*c*(m+1)]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) + 
  (a*d*m+b*c*(m+1))/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[a*d*m+b*c*(m+1)] && RationalQ[m] && m<-1/2


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(a*f*(2*m+1)) + 
  (a*d*m+b*c*(m+1))/(a*b*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[a*d*m+b*c*(m+1)] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) + 
  (a*d*m+b*c*(m+1))/(b*(m+1))*Int[(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[a*d*m+b*c*(m+1)] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  d*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(f*(m+1)) + 
  (a*d*m+b*c*(m+1))/(b*(m+1))*Int[(a+b*Cos[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[a*d*m+b*c*(m+1)] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Sin[e+f*x])^(m-1)*Simp[b*d*m+a*c*(m+1)+(a*d*m+b*c*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  d*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Cos[e+f*x])^(m-1)*Simp[b*d*m+a*c*(m+1)+(a*d*m+b*c*(m+1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[(a*c-b*d)*(m+1)-(c*b-a*d)*(m+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*Simp[(a*c-b*d)*(m+1)-(c*b-a*d)*(m+2)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*Sqrt[2]*c*(a+b*Sin[e+f*x])^m*(c-d*Sin[e+f*x])*Sqrt[(c+d*Sin[e+f*x])/c]/(d*f*Cos[e+f*x]*((c*(a+b*Sin[e+f*x]))/(a*c+b*d))^m)*
    AppellF1[1/2,-1/2,-m,3/2,(c-d*Sin[e+f*x])/(2*c),(b*(c-d*Sin[e+f*x]))/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[IntegerQ[2*m]]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  2*Sqrt[2]*c*(a+b*Cos[e+f*x])^m*(c-d*Cos[e+f*x])*Sqrt[(c+d*Cos[e+f*x])/c]/(d*f*Sin[e+f*x]*((c*(a+b*Cos[e+f*x]))/(a*c+b*d))^m)*
    AppellF1[1/2,-1/2,-m,3/2,(c-d*Cos[e+f*x])/(2*c),(b*(c-d*Cos[e+f*x]))/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[IntegerQ[2*m]]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)/b*Int[(a+b*Sin[e+f*x])^m,x] + d/b*Int[(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)/b*Int[(a+b*Cos[e+f*x])^m,x] + d/b*Int[(a+b*Cos[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2]


Int[(b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  2*c*d/b*Int[(b*Sin[e+f*x])^(m+1),x] + Int[(b*Sin[e+f*x])^m*(c^2+d^2*Sin[e+f*x]^2),x] /;
FreeQ[{b,c,d,e,f,m},x]


Int[(b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^2,x_Symbol] :=
  2*c*d/b*Int[(b*Cos[e+f*x])^(m+1),x] + Int[(b*Cos[e+f*x])^m*(c^2+d^2*Cos[e+f*x]^2),x] /;
FreeQ[{b,c,d,e,f,m},x]


Int[sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(a*m-b*(2*m+1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[cos[e_.+f_.*x_]^2*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(a*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(a*m-b*(2*m+1)*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*(b*(m+1)-a*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[cos[e_.+f_.*x_]^2*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Cos[e+f*x])^m*(b*(m+1)-a*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*c*d*(m-1)+b*(d^2+c^2*(m+1))+d*(a*d*(m-1)+b*c*(m+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^2,x_Symbol] :=
  -(b*c-a*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*Simp[a*c*d*(m-1)+b*(d^2+c^2*(m+1))+d*(a*d*(m-1)+b*c*(m+2))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  -d^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[b*(d^2*(m+1)+c^2*(m+2))-d*(a*d-2*b*c*(m+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^2,x_Symbol] :=
  d^2*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Cos[e+f*x])^m*Simp[b*(d^2*(m+1)+c^2*(m+2))-d*(a*d-2*b*c*(m+2))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  -(b^2*c^2-2*a*b*c*d+a^2*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) - 
  1/(b*(m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*
    Simp[b*(m+1)*(2*b*c*d-a*(c^2+d^2))+(a^2*d^2-2*a*b*c*d*(m+2)+b^2*(d^2*(m+1)+c^2*(m+2)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && (IntegerQ[2*m] || NonzeroQ[c^2-d^2])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^2,x_Symbol] :=
  (b^2*c^2-2*a*b*c*d+a^2*d^2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) - 
  1/(b*(m+1)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*
    Simp[b*(m+1)*(2*b*c*d-a*(c^2+d^2))+(a^2*d^2-2*a*b*c*d*(m+2)+b^2*(d^2*(m+1)+c^2*(m+2)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && (IntegerQ[2*m] || NonzeroQ[c^2-d^2])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  -d^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[b*(d^2*(m+1)+c^2*(m+2))-d*(a*d-2*b*c*(m+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && 
  (IntegerQ[2*m] || NonzeroQ[c^2-d^2])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^2,x_Symbol] :=
  d^2*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Cos[e+f*x])^m*Simp[b*(d^2*(m+1)+c^2*(m+2))-d*(a*d-2*b*c*(m+2))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && 
  (IntegerQ[2*m] || NonzeroQ[c^2-d^2])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)) + 
  b^2/(d*(n+1)*(b*c+a*d))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[a*c*(m-2)-b*d*(m-2*n-4)-(b*c*(m-1)-a*d*(m+2*n+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>1 && n<-1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m+1/2] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*(b*c-a*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)) + 
  b^2/(d*(n+1)*(b*c+a*d))*Int[(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^(n+1)*
    Simp[a*c*(m-2)-b*d*(m-2*n-4)-(b*c*(m-1)-a*d*(m+2*n+1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>1 && n<-1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m+1/2] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^n*
    Simp[a*b*c*(m-2)+b^2*d*(n+1)+a^2*d*(m+n)-b*(b*c*(m-1)-a*d*(3*m+2*n-2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>1 && 
  Not[RationalQ[n] && n<-1] && (IntegersQ[2*m,2*n] || IntegerQ[m+1/2] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^n*
    Simp[a*b*c*(m-2)+b^2*d*(n+1)+a^2*d*(m+n)-b*(b*c*(m-1)-a*d*(3*m+2*n-2))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>1 && 
  Not[RationalQ[n] && n<-1] && (IntegersQ[2*m,2*n] || IntegerQ[m+1/2] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*Simp[a*d*n-b*c*(m+1)-b*d*(m+n+1)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 0<n<1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n-1)*Simp[a*d*n-b*c*(m+1)-b*d*(m+n+1)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 0<n<1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-2)*
    Simp[b*(c^2*(m+1)+d^2*(n-1))+a*c*d*(m-n+1)+d*(a*d*(m-n+1)+b*c*(m+n))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && n>1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b*c-a*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n-1)/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n-2)*
    Simp[b*(c^2*(m+1)+d^2*(n-1))+a*c*d*(m-n+1)+d*(a*d*(m-n+1)+b*c*(m+n))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && n>1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(a*f*(2*m+1)*(b*c-a*d)) + 
  1/(a*(2*m+1)*(b*c-a*d))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[b*c*(m+1)-a*d*(2*m+n+2)+b*d*(m+n+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  Not[RationalQ[n] && n>0] && (IntegersQ[2*m,2*n] || IntegerQ[m] && ZeroQ[c])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(a*f*(2*m+1)*(b*c-a*d)) + 
  1/(a*(2*m+1)*(b*c-a*d))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[b*c*(m+1)-a*d*(2*m+n+2)+b*d*(m+n+2)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  Not[RationalQ[n] && n>0] && (IntegersQ[2*m,2*n] || IntegerQ[m] && ZeroQ[c])


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n-1)/(a*f*(a+b*Sin[e+f*x])) - 
  d/(a*b)*Int[(c+d*Sin[e+f*x])^(n-2)*Simp[b*d*(n-1)-a*c*n+(b*c*(n-1)-a*d*n)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>1 && 
  (IntegerQ[2*n] || ZeroQ[c])


Int[(c_.+d_.*cos[e_.+f_.*x_])^n_/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*Sin[e+f*x]*(c+d*Cos[e+f*x])^(n-1)/(a*f*(a+b*Cos[e+f*x])) - 
  d/(a*b)*Int[(c+d*Cos[e+f*x])^(n-2)*Simp[b*d*(n-1)-a*c*n+(b*c*(n-1)-a*d*n)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>1 && 
  (IntegerQ[2*n] || ZeroQ[c])


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b^2*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(a*f*(b*c-a*d)*(a+b*Sin[e+f*x])) + 
  d/(a*(b*c-a*d))*Int[(c+d*Sin[e+f*x])^n*(a*n-b*(n+1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n<0 && (IntegerQ[2*n] || ZeroQ[c])


Int[(c_.+d_.*cos[e_.+f_.*x_])^n_/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b^2*Sin[e+f*x]*(c+d*Cos[e+f*x])^(n+1)/(a*f*(b*c-a*d)*(a+b*Cos[e+f*x])) + 
  d/(a*(b*c-a*d))*Int[(c+d*Cos[e+f*x])^n*(a*n-b*(n+1)*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n<0 && (IntegerQ[2*n] || ZeroQ[c])


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(a*f*(a+b*Sin[e+f*x])) + 
  d*n/(a*b)*Int[(c+d*Sin[e+f*x])^(n-1)*(a-b*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && (IntegerQ[2*n] || ZeroQ[c])


Int[(c_.+d_.*cos[e_.+f_.*x_])^n_/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b*Sin[e+f*x]*(c+d*Cos[e+f*x])^n/(a*f*(a+b*Cos[e+f*x])) + 
  d*n/(a*b)*Int[(c+d*Cos[e+f*x])^(n-1)*(a-b*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && (IntegerQ[2*n] || ZeroQ[c])


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Sin[e+f*x]]) + 
  2*n*(b*c+a*d)/(b*(2*n+1))*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>0 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  2*b*Sin[e+f*x]*(c+d*Cos[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Cos[e+f*x]]) + 
  2*n*(b*c+a*d)/(b*(2*n+1))*Int[Sqrt[a+b*Cos[e+f*x]]*(c+d*Cos[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>0 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_.+d_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  -2*b^2*Cos[e+f*x]/(f*(b*c+a*d)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/(c_.+d_.*cos[e_.+f_.*x_])^(3/2),x_Symbol] :=
  2*b^2*Sin[e+f*x]/(f*(b*c+a*d)*Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*c-a*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)*Sqrt[a+b*Sin[e+f*x]]) + 
  (2*n+3)*(b*c-a*d)/(2*b*(n+1)*(c^2-d^2))*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n<-1 && NonzeroQ[2*n+3] && IntegerQ[2*n]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b*c-a*d)*Sin[e+f*x]*(c+d*Cos[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)*Sqrt[a+b*Cos[e+f*x]]) + 
  (2*n+3)*(b*c-a*d)/(2*b*(n+1)*(c^2-d^2))*Int[Sqrt[a+b*Cos[e+f*x]]*(c+d*Cos[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*b/f*Subst[Int[1/(b*c+a*d-d*x^2),x],x,b*Cos[e+f*x]/Sqrt[a+b*Sin[e+f*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  2*b/f*Subst[Int[1/(b*c+a*d-d*x^2),x],x,b*Sin[e+f*x]/Sqrt[a+b*Cos[e+f*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2/f*Subst[Int[1/Sqrt[1-x^2/a],x],x,b*Cos[e+f*x]/Sqrt[a+b*Sin[e+f*x]]] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && ZeroQ[d-a/b]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/Sqrt[d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  2/f*Subst[Int[1/Sqrt[1-x^2/a],x],x,b*Sin[e+f*x]/Sqrt[a+b*Cos[e+f*x]]] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && ZeroQ[d-a/b]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*b/f*Subst[Int[1/(b+d*x^2),x],x,b*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/Sqrt[c_.+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  2*b/f*Subst[Int[1/(b+d*x^2),x],x,b*Sin[e+f*x]/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(f*Sqrt[a+b*Sin[e+f*x]]*(a*(c+d*Sin[e+f*x])/(a*c+b*d))^n)*
    Hypergeometric2F1[1/2,-n,3/2,d*(a-b*Sin[e+f*x])/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[IntegerQ[2*n]]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  2*b*Sin[e+f*x]*(c+d*Cos[e+f*x])^n/(f*Sqrt[a+b*Cos[e+f*x]]*(a*(c+d*Cos[e+f*x])/(a*c+b*d))^n)*
    Hypergeometric2F1[1/2,-n,3/2,d*(a-b*Cos[e+f*x])/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[IntegerQ[2*n]]


Int[Sqrt[c_.+d_.*sin[e_.+f_.*x_]]/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  d/b*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + (b*c-a*d)/b*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[c_.+d_.*cos[e_.+f_.*x_]]/Sqrt[a_+b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  d/b*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]],x] + (b*c-a*d)/b*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*d*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Sin[e+f*x]]) - 
  1/(b*(2*n-1))*Int[(c+d*Sin[e+f*x])^(n-2)/Sqrt[a+b*Sin[e+f*x]]*
    Simp[a*c*d-b*(2*d^2*(n-1)+c^2*(2*n-1))+d*(a*d-b*c*(4*n-3))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[(c_.+d_.*cos[e_.+f_.*x_])^n_/Sqrt[a_+b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  2*d*Sin[e+f*x]*(c+d*Cos[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Cos[e+f*x]]) - 
  1/(b*(2*n-1))*Int[(c+d*Cos[e+f*x])^(n-2)/Sqrt[a+b*Cos[e+f*x]]*
    Simp[a*c*d-b*(2*d^2*(n-1)+c^2*(2*n-1))+d*(a*d-b*c*(4*n-3))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -d*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)*Sqrt[a+b*Sin[e+f*x]]) - 
  1/(2*b*(n+1)*(c^2-d^2))*Int[(c+d*Sin[e+f*x])^(n+1)*Simp[a*d-2*b*c*(n+1)+b*d*(2*n+3)*Sin[e+f*x],x]/Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(c_.+d_.*cos[e_.+f_.*x_])^n_/Sqrt[a_+b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  d*Sin[e+f*x]*(c+d*Cos[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)*Sqrt[a+b*Cos[e+f*x]]) - 
  1/(2*b*(n+1)*(c^2-d^2))*Int[(c+d*Cos[e+f*x])^(n+1)*Simp[a*d-2*b*c*(n+1)+b*d*(2*n+3)*Cos[e+f*x],x]/Sqrt[a+b*Cos[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/Sqrt[a+b*Sin[e+f*x]],x] - d/(b*c-a*d)*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/Sqrt[a+b*Cos[e+f*x]],x] - d/(b*c-a*d)*Int[Sqrt[a+b*Cos[e+f*x]]/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -Sqrt[2]/(Sqrt[a]*f)*Subst[Int[1/Sqrt[1-x^2],x],x,b*Cos[e+f*x]/(a+b*Sin[e+f*x])] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && ZeroQ[d-a/b] && PositiveQ[a]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[2]/(Sqrt[a]*f)*Subst[Int[1/Sqrt[1-x^2],x],x,b*Sin[e+f*x]/(a+b*Cos[e+f*x])] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && ZeroQ[d-a/b] && PositiveQ[a]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*a/f*Subst[Int[1/(2*b^2-(a*c-b*d)*x^2),x],x,b*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  2*a/f*Subst[Int[1/(2*b^2-(a*c-b*d)*x^2),x],x,b*Sin[e+f*x]/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)/(f*(m+n)) + 
  1/(b*(m+n))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-2)*
    Simp[d*(a*c*m+b*d*(n-1))+b*c^2*(m+n)+d*(a*d*m+b*c*(m+2*n-1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>1 && IntegerQ[n]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  d*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n-1)/(f*(m+n)) + 
  1/(b*(m+n))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n-2)*
    Simp[d*(a*c*m+b*d*(n-1))+b*c^2*(m+n)+d*(a*d*m+b*c*(m+2*n-1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>1 && IntegerQ[n]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2^(m+1)*b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*((a*c+b*d)/a)^(m+1)*((a+b*Sin[e+f*x])/a)^(m+1))*
    Hypergeometric2F1[1/2,m+1,3/2,-(a*c-b*d)*(a-b*Sin[e+f*x])/((a*c+b*d)*(a+b*Sin[e+f*x]))] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[m+n+1] && 
  (PositiveQ[c^2-d^2] && PositiveQ[b*c/a] || NegativeQ[c^2-d^2] && PositiveQ[b*d/a])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  2^(m+1)*b*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(a*f*((a*c+b*d)/a)^(m+1)*((a+b*Cos[e+f*x])/a)^(m+1))*
    Hypergeometric2F1[1/2,m+1,3/2,-(a*c-b*d)*(a-b*Cos[e+f*x])/((a*c+b*d)*(a+b*Cos[e+f*x]))] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[m+n+1] && 
  (PositiveQ[c^2-d^2] && PositiveQ[b*c/a] || NegativeQ[c^2-d^2] && PositiveQ[b*d/a])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -(c+d*Sin[e+f*x])^(n+1)/(-c-d*Sin[e+f*x])^(n+1)*Int[(a+b*Sin[e+f*x])^m*(-c-d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[m+n+1] && 
  (PositiveQ[c^2-d^2] && NegativeQ[b*c/a] || NegativeQ[c^2-d^2] && NegativeQ[b*d/a])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -(c+d*Cos[e+f*x])^(n+1)/(-c-d*Cos[e+f*x])^(n+1)*Int[(a+b*Cos[e+f*x])^m*(-c-d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[m+n+1] && 
  (PositiveQ[c^2-d^2] && NegativeQ[b*c/a] || NegativeQ[c^2-d^2] && NegativeQ[b*d/a])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -Sqrt[2]*2^m*a^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)/(f*(b*c+a*d)*(c+d*Sin[e+f*x])^m)*
    ((b*c+a*d)*(a+b*Sin[e+f*x])/(a*b*(c+d*Sin[e+f*x])))^(1/2-m)*
    Hypergeometric2F1[1/2,1/2-m,3/2,((b*c-a*d)*(a-b*Sin[e+f*x]))/(2*a*b*(c+d*Sin[e+f*x]))] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[m+n+1]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  Sqrt[2]*2^m*a^2*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-1)/(f*(b*c+a*d)*(c+d*Cos[e+f*x])^m)*
    ((b*c+a*d)*(a+b*Cos[e+f*x])/(a*b*(c+d*Cos[e+f*x])))^(1/2-m)*
    Hypergeometric2F1[1/2,1/2-m,3/2,((b*c-a*d)*(a-b*Cos[e+f*x]))/(2*a*b*(c+d*Cos[e+f*x]))] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[m+n+1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -Sqrt[2]*2^m*a^m*(a-b*Sin[e+f*x])*(c+d*Sin[e+f*x])^n*Sqrt[(a+b*Sin[e+f*x])/a]/
    (b*f*Cos[e+f*x]*((a*(c+d*Sin[e+f*x]))/(a*c+b*d))^n)*
    AppellF1[1/2,1/2-m,-n,3/2,(a-b*Sin[e+f*x])/(2*a),(d*(a-b*Sin[e+f*x]))/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && IntegerQ[m] && Not[IntegerQ[2*n]]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  Sqrt[2]*2^m*a^m*(a-b*Cos[e+f*x])*(c+d*Cos[e+f*x])^n*Sqrt[(a+b*Cos[e+f*x])/a]/
    (b*f*Sin[e+f*x]*((a*(c+d*Cos[e+f*x]))/(a*c+b*d))^n)*
    AppellF1[1/2,1/2-m,-n,3/2,(a-b*Cos[e+f*x])/(2*a),(d*(a-b*Cos[e+f*x]))/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && IntegerQ[m] && Not[IntegerQ[2*n]]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2^(m+1/2)*(a-b*Sin[e+f*x])*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/
    (b*f*Cos[e+f*x]*((a+b*Sin[e+f*x])/a)^(m-1/2)*((a*(c+d*Sin[e+f*x]))/(a*c+b*d))^n)*
    AppellF1[1/2,1/2-m,-n,3/2,(a-b*Sin[e+f*x])/(2*a),d*(a-b*Sin[e+f*x])/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && (Not[IntegerQ[m]] || NonzeroQ[c])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  2^(m+1/2)*(a-b*Cos[e+f*x])*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/
    (b*f*Sin[e+f*x]*((a+b*Cos[e+f*x])/a)^(m-1/2)*((a*(c+d*Cos[e+f*x]))/(a*c+b*d))^n)*
    AppellF1[1/2,1/2-m,-n,3/2,(a-b*Cos[e+f*x])/(2*a),d*(a-b*Cos[e+f*x])/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && (Not[IntegerQ[m]] || NonzeroQ[c])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b^2*c^2-2*a*b*c*d+a^2*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^(m-3)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[b*(m-2)*(b*c-a*d)^2+a*d*(n+1)*(c*(a^2+b^2)-2*a*b*d)+
      (b*(n+1)*(a*b*c^2+c*d*(a^2+b^2)-3*a*b*d^2)-a*(n+2)*(b*c-a*d)^2)*Sin[e+f*x]+
      b*(b^2*(c^2-d^2)-m*(b*c-a*d)^2+d*n*(2*a*b*c-d*(a^2+b^2)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>2 && n<-1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  (b^2*c^2-2*a*b*c*d+a^2*d^2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Cos[e+f*x])^(m-3)*(c+d*Cos[e+f*x])^(n+1)*
    Simp[b*(m-2)*(b*c-a*d)^2+a*d*(n+1)*(c*(a^2+b^2)-2*a*b*d)+
      (b*(n+1)*(a*b*c^2+c*d*(a^2+b^2)-3*a*b*d^2)-a*(n+2)*(b*c-a*d)^2)*Cos[e+f*x]+
      b*(b^2*(c^2-d^2)-m*(b*c-a*d)^2+d*n*(2*a*b*c-d*(a^2+b^2)))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>2 && n<-1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Sin[e+f*x])^(m-3)*(c+d*Sin[e+f*x])^n*
    Simp[a^3*d*(m+n)+b^2*(b*c*(m-2)+a*d*(n+1))-
      b*(a*b*c-b^2*d*(m+n-1)-3*a^2*d*(m+n))*Sin[e+f*x]-
      b^2*(b*c*(m-1)-a*d*(3*m+2*n-2))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>2 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[IntegerQ[n] && n>2 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Cos[e+f*x])^(m-3)*(c+d*Cos[e+f*x])^n*
    Simp[a^3*d*(m+n)+b^2*(b*c*(m-2)+a*d*(n+1))-
      b*(a*b*c-b^2*d*(m+n-1)-3*a^2*d*(m+n))*Cos[e+f*x]-
      b^2*(b*c*(m-1)-a*d*(3*m+2*n-2))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>2 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[IntegerQ[n] && n>2 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[Sqrt[d_.*sin[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  -2*a*d*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) - 
  d^2/(a^2-b^2)*Int[Sqrt[a+b*Sin[e+f*x]]/(d*Sin[e+f*x])^(3/2),x] /; 
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[d_.*cos[e_.+f_.*x_]]/(a_+b_.*cos[e_.+f_.*x_])^(3/2),x_Symbol] :=
  2*a*d*Sin[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Cos[e+f*x]]*Sqrt[d*Cos[e+f*x]]) - 
  d^2/(a^2-b^2)*Int[Sqrt[a+b*Cos[e+f*x]]/(d*Cos[e+f*x])^(3/2),x] /; 
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[c_+d_.*sin[e_.+f_.*x_]]/(a_.+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  (c-d)/(a-b)*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] - 
  (b*c-a*d)/(a-b)*Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /; 
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[c_+d_.*cos[e_.+f_.*x_]]/(a_.+b_.*cos[e_.+f_.*x_])^(3/2),x_Symbol] :=
  (c-d)/(a-b)*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]),x] - 
  (b*c-a*d)/(a-b)*Int[(1+Cos[e+f*x])/((a+b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]]),x] /; 
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[a*c*(m+1)+b*d*n+(a*d*(m+1)-b*c*(m+2))*Sin[e+f*x]-b*d*(m+n+2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 0<n<1 && 
  IntegersQ[2*m,2*n]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n-1)*
    Simp[a*c*(m+1)+b*d*n+(a*d*(m+1)-b*c*(m+2))*Cos[e+f*x]-b*d*(m+n+2)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 0<n<1 && 
  IntegersQ[2*m,2*n]


Int[(d_.*sin[e_.+f_.*x_])^(3/2)/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  d/b*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] - 
  a*d/b*Int[Sqrt[d*Sin[e+f*x]]/(a+b*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*cos[e_.+f_.*x_])^(3/2)/(a_+b_.*cos[e_.+f_.*x_])^(3/2),x_Symbol] :=
  d/b*Int[Sqrt[d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]],x] - 
  a*d/b*Int[Sqrt[d*Cos[e+f*x]]/(a+b*Cos[e+f*x])^(3/2),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(c_+d_.*sin[e_.+f_.*x_])^(3/2)/(a_.+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  d^2/b^2*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  (b*c-a*d)/b^2*Int[Simp[b*c+a*d+2*b*d*Sin[e+f*x],x]/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(c_+d_.*cos[e_.+f_.*x_])^(3/2)/(a_.+b_.*cos[e_.+f_.*x_])^(3/2),x_Symbol] :=
  d^2/b^2*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]],x] + 
  (b*c-a*d)/b^2*Int[Simp[b*c+a*d+2*b*d*Cos[e+f*x],x]/((a+b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-2)*
    Simp[c*(a*c-b*d)*(m+1)+d*(b*c-a*d)*(n-1)+(d*(a*c-b*d)*(m+1)-c*(b*c-a*d)*(m+2))*Sin[e+f*x]-d*(b*c-a*d)*(m+n+1)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 1<n<2 && 
  IntegersQ[2*m,2*n]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*c-a*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n-2)*
    Simp[c*(a*c-b*d)*(m+1)+d*(b*c-a*d)*(n-1)+(d*(a*c-b*d)*(m+1)-c*(b*c-a*d)*(m+2))*Cos[e+f*x]-d*(b*c-a*d)*(m+n+1)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 1<n<2 && 
  IntegersQ[2*m,2*n]


Int[1/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2*b*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) + 
  d/(a^2-b^2)*Int[(b+a*Sin[e+f*x])/(Sqrt[a+b*Sin[e+f*x]]*(d*Sin[e+f*x])^(3/2)),x] /; 
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[1/((a_+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  -2*b*Sin[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Cos[e+f*x]]*Sqrt[d*Cos[e+f*x]]) + 
  d/(a^2-b^2)*Int[(b+a*Cos[e+f*x])/(Sqrt[a+b*Cos[e+f*x]]*(d*Cos[e+f*x])^(3/2)),x] /; 
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  1/(a-b)*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] - 
  b/(a-b)*Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[1/((a_.+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  1/(a-b)*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]),x] - 
  b/(a-b)*Int[(1+Cos[e+f*x])/((a+b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[a*(b*c-a*d)*(m+1)+b^2*d*(m+n+2)-(b^2*c+b*(b*c-a*d)*(m+1))*Sin[e+f*x]-b^2*d*(m+n+3)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  IntegersQ[2*m,2*n] && 
  (ZeroQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || ZeroQ[a])])


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[a*(b*c-a*d)*(m+1)+b^2*d*(m+n+2)-(b^2*c+b*(b*c-a*d)*(m+1))*Cos[e+f*x]-b^2*d*(m+n+3)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  IntegersQ[2*m,2*n] && 
  (ZeroQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || ZeroQ[a])])


Int[Sqrt[c_.+d_.*sin[e_.+f_.*x_]]/(a_.+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[1/Sqrt[c+d*Sin[e+f*x]],x] + 
  (b*c-a*d)/b*Int[1/((a+b*Sin[e+f*x])*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[c_.+d_.*cos[e_.+f_.*x_]]/(a_.+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[1/Sqrt[c+d*Cos[e+f*x]],x] + 
  (b*c-a*d)/b*Int[1/((a+b*Cos[e+f*x])*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^(3/2)/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b/d*Int[Sqrt[a+b*Sin[e+f*x]],x] - (b*c-a*d)/d*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^(3/2)/(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b/d*Int[Sqrt[a+b*Cos[e+f*x]],x] - (b*c-a*d)/d*Int[Sqrt[a+b*Cos[e+f*x]]/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2/(f*(a+b)*Sqrt[c+d])*EllipticPi[2*b/(a+b),(e+f*x)/2-Pi/4,2*d/(c+d)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PositiveQ[c+d]


Int[1/((a_.+b_.*cos[e_.+f_.*x_])*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  2/(f*(a+b)*Sqrt[c+d])*EllipticPi[2*b/(a+b),(e+f*x)/2,2*d/(c+d)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PositiveQ[c+d]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2/(f*(a-b)*Sqrt[c-d])*EllipticPi[-2*b/(a-b),(e+f*x)/2+Pi/4,-2*d/(c-d)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PositiveQ[c-d]


Int[1/((a_.+b_.*cos[e_.+f_.*x_])*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  2/(f*(a-b)*Sqrt[c-d])*EllipticPi[-2*b/(a-b),(e+f*x)/2+Pi/2,-2*d/(c-d)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PositiveQ[c-d]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[(c+d*Sin[e+f*x])/(c+d)]/Sqrt[c+d*Sin[e+f*x]]*Int[1/((a+b*Sin[e+f*x])*Sqrt[c/(c+d)+d/(c+d)*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[PositiveQ[c+d]]


Int[1/((a_.+b_.*cos[e_.+f_.*x_])*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[(c+d*Cos[e+f*x])/(c+d)]/Sqrt[c+d*Cos[e+f*x]]*Int[1/((a+b*Cos[e+f*x])*Sqrt[c/(c+d)+d/(c+d)*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[PositiveQ[c+d]]


Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  2*c*Rt[b*(c+d),2]*Tan[e+f*x]*Sqrt[1+Csc[e+f*x]]*Sqrt[1-Csc[e+f*x]]/(d*f*Sqrt[c^2-d^2])*
    EllipticPi[(c+d)/d,ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f},x] && PositiveQ[c^2-d^2] && PosQ[(c+d)/b] && PositiveQ[c^2]


Int[Sqrt[b_.*cos[e_.+f_.*x_]]/Sqrt[c_+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  -2*c*Rt[b*(c+d),2]*Cot[e+f*x]*Sqrt[1+Sec[e+f*x]]*Sqrt[1-Sec[e+f*x]]/(d*f*Sqrt[c^2-d^2])*
    EllipticPi[(c+d)/d,ArcSin[Sqrt[c+d*Cos[e+f*x]]/Sqrt[b*Cos[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f},x] && PositiveQ[c^2-d^2] && PosQ[(c+d)/b] && PositiveQ[c^2]


Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  2*b*Tan[e+f*x]/(d*f)*Rt[(c+d)/b,2]*Sqrt[c*(1+Csc[e+f*x])/(c-d)]*Sqrt[c*(1-Csc[e+f*x])/(c+d)]*
    EllipticPi[(c+d)/d,ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[c^2-d^2] && PosQ[(c+d)/b]


Int[Sqrt[b_.*cos[e_.+f_.*x_]]/Sqrt[c_+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  -2*b*Cot[e+f*x]/(d*f)*Rt[(c+d)/b,2]*Sqrt[c*(1+Sec[e+f*x])/(c-d)]*Sqrt[c*(1-Sec[e+f*x])/(c+d)]*
    EllipticPi[(c+d)/d,ArcSin[Sqrt[c+d*Cos[e+f*x]]/Sqrt[b*Cos[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[c^2-d^2] && PosQ[(c+d)/b]


Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b*Sin[e+f*x]]/Sqrt[-b*Sin[e+f*x]]*Int[Sqrt[-b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[c^2-d^2] && NegQ[(c+d)/b]


Int[Sqrt[b_.*cos[e_.+f_.*x_]]/Sqrt[c_+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b*Cos[e+f*x]]/Sqrt[-b*Cos[e+f*x]]*Int[Sqrt[-b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]],x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[c^2-d^2] && NegQ[(c+d)/b]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  a*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]),x] + 
  b/d*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/Sqrt[d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  a*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[d*Cos[e+f*x]]),x] + 
  b/d*Int[Sqrt[d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  2*(a+b*Sin[e+f*x])/(d*f*Rt[(a+b)/(c+d),2]*Cos[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Sin[e+f*x])/((c-d)*(a+b*Sin[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Sin[e+f*x])/((c+d)*(a+b*Sin[e+f*x]))]*
    EllipticPi[b*(c+d)/(d*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PosQ[(a+b)/(c+d)]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/Sqrt[c_+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  -2*(a+b*Cos[e+f*x])/(d*f*Rt[(a+b)/(c+d),2]*Sin[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Cos[e+f*x])/((c-d)*(a+b*Cos[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Cos[e+f*x])/((c+d)*(a+b*Cos[e+f*x]))]*
    EllipticPi[b*(c+d)/(d*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PosQ[(a+b)/(c+d)]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[-c-d*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]]*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[-c-d*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NegQ[(a+b)/(c+d)]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/Sqrt[c_+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[-c-d*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]]*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[-c-d*Cos[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NegQ[(a+b)/(c+d)]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*d/(f*Sqrt[a+b*d])*EllipticF[ArcSin[Cos[e+f*x]/(1+d*Sin[e+f*x])],-(a-b*d)/(a+b*d)] /;
FreeQ[{a,b,d,e,f},x] && NegativeQ[a^2-b^2] && ZeroQ[d^2-1] && PositiveQ[b*d]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  2*d/(f*Sqrt[a+b*d])*EllipticF[ArcSin[Sin[e+f*x]/(1+d*Cos[e+f*x])],-(a-b*d)/(a+b*d)] /;
FreeQ[{a,b,d,e,f},x] && NegativeQ[a^2-b^2] && ZeroQ[d^2-1] && PositiveQ[b*d]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[Sign[b]*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[Sign[b]*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f},x] && NegativeQ[a^2-b^2] && PositiveQ[b^2] && Not[ZeroQ[d^2-1] && PositiveQ[b*d]]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[Sign[b]*Cos[e+f*x]]/Sqrt[d*Cos[e+f*x]]*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[Sign[b]*Cos[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f},x] && NegativeQ[a^2-b^2] && PositiveQ[b^2] && Not[ZeroQ[d^2-1] && PositiveQ[b*d]]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*Sqrt[a^2]*Sqrt[-Cot[e+f*x]^2]/(a*f*Sqrt[a^2-b^2]*Cot[e+f*x])*Rt[(a+b)/d,2]*
    EllipticF[ArcSin[Sqrt[a+b*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]/Rt[(a+b)/d,2]],-(a+b)/(a-b)] /;
FreeQ[{a,b,d,e,f},x] && PositiveQ[a^2-b^2] && PosQ[(a+b)/d] && PositiveQ[a^2]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  2*Sqrt[a^2]*Sqrt[-Tan[e+f*x]^2]/(a*f*Sqrt[a^2-b^2]*Tan[e+f*x])*Rt[(a+b)/d,2]*
    EllipticF[ArcSin[Sqrt[a+b*Cos[e+f*x]]/Sqrt[d*Cos[e+f*x]]/Rt[(a+b)/d,2]],-(a+b)/(a-b)] /;
FreeQ[{a,b,d,e,f},x] && PositiveQ[a^2-b^2] && PosQ[(a+b)/d] && PositiveQ[a^2]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*Tan[e+f*x]/(a*f)*Rt[(a+b)/d,2]*Sqrt[a*(1-Csc[e+f*x])/(a+b)]*Sqrt[a*(1+Csc[e+f*x])/(a-b)]*
    EllipticF[ArcSin[Sqrt[a+b*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]/Rt[(a+b)/d,2]],-(a+b)/(a-b)] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && PosQ[(a+b)/d]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  2*Cot[e+f*x]/(a*f)*Rt[(a+b)/d,2]*Sqrt[a*(1-Sec[e+f*x])/(a+b)]*Sqrt[a*(1+Sec[e+f*x])/(a-b)]*
    EllipticF[ArcSin[Sqrt[a+b*Cos[e+f*x]]/Sqrt[d*Cos[e+f*x]]/Rt[(a+b)/d,2]],-(a+b)/(a-b)] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && PosQ[(a+b)/d]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-d*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[-d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && NegQ[(a+b)/d]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-d*Cos[e+f*x]]/Sqrt[d*Cos[e+f*x]]*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[-d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && NegQ[(a+b)/d]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2*(c+d*Sin[e+f*x])/(f*(b*c-a*d)*Rt[(c+d)/(a+b),2]*Cos[e+f*x])*
    Sqrt[(b*c-a*d)*(1-Sin[e+f*x])/((a+b)*(c+d*Sin[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1+Sin[e+f*x])/((a-b)*(c+d*Sin[e+f*x]))]*
    EllipticF[ArcSin[Rt[(c+d)/(a+b),2]*(Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]])],(a+b)*(c-d)/((a-b)*(c+d))] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PosQ[(c+d)/(a+b)]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  -2*(c+d*Cos[e+f*x])/(f*(b*c-a*d)*Rt[(c+d)/(a+b),2]*Sin[e+f*x])*
    Sqrt[(b*c-a*d)*(1-Cos[e+f*x])/((a+b)*(c+d*Cos[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1+Cos[e+f*x])/((a-b)*(c+d*Cos[e+f*x]))]*
    EllipticF[ArcSin[Rt[(c+d)/(a+b),2]*(Sqrt[a+b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]])],(a+b)*(c-d)/((a-b)*(c+d))] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PosQ[(c+d)/(a+b)]


Int[1/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-a-b*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]*Int[1/(Sqrt[-a-b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NegQ[(c+d)/(a+b)]


Int[1/(Sqrt[a_.+b_.*cos[e_.+f_.*x_]]*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-a-b*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]]*Int[1/(Sqrt[-a-b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NegQ[(c+d)/(a+b)]


Int[(d_.*sin[e_.+f_.*x_])^(3/2)/Sqrt[a_.+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -a*d/(2*b)*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] + 
  d/(2*b)*Int[Sqrt[d*Sin[e+f*x]]*(a+2*b*Sin[e+f*x])/Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*cos[e_.+f_.*x_])^(3/2)/Sqrt[a_.+b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  -a*d/(2*b)*Int[Sqrt[d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]],x] + 
  d/(2*b)*Int[Sqrt[d*Cos[e+f*x]]*(a+2*b*Cos[e+f*x])/Sqrt[a+b*Cos[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[a^2*c*d*(m+n)+b*d*(b*c*(m-1)+a*d*n)+
      (a*d*(2*b*c+a*d)*(m+n)-b*d*(a*c-b*d*(m+n-1)))*Sin[e+f*x]+
      b*d*(b*c*n+a*d*(2*m+n-1))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && 0<m<2 && -1<n<2 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^n/(f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^(n-1)*
    Simp[a^2*c*d*(m+n)+b*d*(b*c*(m-1)+a*d*n)+
      (a*d*(2*b*c+a*d)*(m+n)-b*d*(a*c-b*d*(m+n-1)))*Cos[e+f*x]+
      b*d*(b*c*n+a*d*(2*m+n-1))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && 0<m<2 && -1<n<2 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b/d*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] - 
  (b*c-a*d)/d*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[m]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b/d*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1),x] - 
  (b*c-a*d)/d*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[m]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


(* ::Subsection::Closed:: *)
(*3.2 (a+b sin)^m (c+d sin)^n (A+B sin)*)


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])*(A_+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*b*f*(2*m+1)) + 
  1/(b^2*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[A*(b*d*m+a*c*(m+1))+B*(b*c-a*d)*m+b*B*d*(2*m+1)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])*(A_+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*(b*c-a*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(a*b*f*(2*m+1)) + 
  1/(b^2*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*Simp[A*(b*d*m+a*c*(m+1))+B*(b*c-a*d)*m+b*B*d*(2*m+1)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])*(A_+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*d*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[b*(A*c*(m+2)+B*d*(m+1))+(A*b*d*(m+2)-B*(a*d-b*c*(m+2)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])*(A_+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*d*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Cos[e+f*x])^m*Simp[b*(A*c*(m+2)+B*d*(m+1))+(A*b*d*(m+2)-B*(a*d-b*c*(m+2)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])*(A_+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*
    Simp[b*(A*(a*c-b*d)-B*(b*c-a*d))*(m+1)-(A*b*(b*c-a*d)*(m+2)-B*(a*b*c*(m+2)-d*(a^2+b^2*(m+1))))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])*(A_+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*(b*c-a*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*
    Simp[b*(A*(a*c-b*d)-B*(b*c-a*d))*(m+1)-(A*b*(b*c-a*d)*(m+2)-B*(a*b*c*(m+2)-d*(a^2+b^2*(m+1))))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])*(A_+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*d*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[b*(A*c*(m+2)+B*d*(m+1))+(A*b*d*(m+2)-B*(a*d-b*c*(m+2)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && Not[ZeroQ[c] && OneQ[m]]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])*(A_+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*d*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Cos[e+f*x])^m*Simp[b*(A*c*(m+2)+B*d*(m+1))+(A*b*d*(m+2)-B*(a*d-b*c*(m+2)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && Not[ZeroQ[c] && OneQ[m]]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -a^m*B*c^m*Cos[e+f*x]^(2*m+1)*(c+d*Sin[e+f*x])^(n-m)/(f*(m+n+1)) /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m] && ZeroQ[A*b*(m+n+1)+a*B*(m-n)]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  a^m*B*c^m*Sin[e+f*x]^(2*m+1)*(c+d*Cos[e+f*x])^(n-m)/(f*(m+n+1)) /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m] && ZeroQ[A*b*(m+n+1)+a*B*(m-n)]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -a^m*c^(m-1)*(B*c-A*d)*Cos[e+f*x]^(2*m+1)*(c+d*Sin[e+f*x])^(n-m)/(f*(2*n+1)) - 
  (B*c*(m-n)-A*d*(m+n+1))/(c*d*(2*n+1))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m] && NegativeIntegerQ[n+1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  a^m*c^(m-1)*(B*c-A*d)*Sin[e+f*x]^(2*m+1)*(c+d*Cos[e+f*x])^(n-m)/(f*(2*n+1)) - 
  (B*c*(m-n)-A*d*(m+n+1))/(c*d*(2*n+1))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m] && NegativeIntegerQ[n+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -a^m*c^m*B*Cos[e+f*x]^(2*m+1)*(c+d*Sin[e+f*x])^(n-m)/(f*(m+n+1)) - 
  (B*c*(m-n)-A*d*(m+n+1))/(d*(m+n+1))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m] && IntegerQ[n+1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  a^m*c^m*B*Sin[e+f*x]^(2*m+1)*(c+d*Cos[e+f*x])^(n-m)/(f*(m+n+1)) - 
  (B*c*(m-n)-A*d*(m+n+1))/(d*(m+n+1))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && PositiveIntegerQ[m] && IntegerQ[n+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a^(m-1)*c^m*(A*b-a*B)*Cos[e+f*x]^(2*m+1)*(c+d*Sin[e+f*x])^(n-m)/(f*(2*m+1)) + 
  (A*b*(m+n+1)+a*B*(m-n))/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && NegativeIntegerQ[m] && IntegerQ[n+1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -a^(m-1)*c^m*(A*b-a*B)*Sin[e+f*x]^(2*m+1)*(c+d*Cos[e+f*x])^(n-m)/(f*(2*m+1)) + 
  (A*b*(m+n+1)+a*B*(m-n))/(a*b*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && NegativeIntegerQ[m] && IntegerQ[n+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a^m*c^m*Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m)*(A+B*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m] && Not[IntegerQ[n] && n^2<m^2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  a^m*c^m*Int[Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m)*(A+B*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && IntegerQ[m] && Not[IntegerQ[n] && n^2<m^2]


Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  (A*b+a*B)/(2*a*b)*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  (B*c+A*d)/(2*c*d)*Int[Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_])/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  (A*b+a*B)/(2*a*b)*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]],x] + 
  (B*c+A*d)/(2*c*d)*Int[Sqrt[c+d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && ZeroQ[A*b*(m+n+1)+a*B*(m-n)] && 
  NonzeroQ[m+1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(f*(m+n+1)) /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && ZeroQ[A*b*(m+n+1)+a*B*(m-n)] && 
  NonzeroQ[m+1/2]


Int[Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] - 
  (B*c-A*d)/d*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2]


Int[Sqrt[a_.+b_.*cos[e_.+f_.*x_]]*(c_+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[Sqrt[a+b*Cos[e+f*x]]*(c+d*Cos[e+f*x])^(n+1),x] - 
  (B*c-A*d)/d*Int[Sqrt[a+b*Cos[e+f*x]]*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) + 
  (a*B*(m-n)+A*b*(m+n+1))/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && 
  (RationalQ[m] && m<-1/2 || NegativeIntegerQ[m+n] && Not[SumSimplerQ[n,1]]) && NonzeroQ[2*m+1]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(a*f*(2*m+1)) + 
  (a*B*(m-n)+A*b*(m+n+1))/(a*b*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && 
  (RationalQ[m] && m<-1/2 || NegativeIntegerQ[m+n] && Not[SumSimplerQ[n,1]]) && NonzeroQ[2*m+1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) - 
  (B*c*(m-n)-A*d*(m+n+1))/(d*(m+n+1))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+1]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(f*(m+n+1)) - 
  (B*c*(m-n)-A*d*(m+n+1))/(d*(m+n+1))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)) /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[m+n+2] && 
  ZeroQ[A*(a*d*m+b*c*(n+1))-B*(a*c*m+b*d*(n+1))]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(B*c-A*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)) /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[m+n+2] && 
  ZeroQ[A*(a*d*m+b*c*(n+1))-B*(a*c*m+b*d*(n+1))]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*b*B*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(2*n+3)*Sqrt[a+b*Sin[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1))]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  2*b*B*Sin[e+f*x]*(c+d*Cos[e+f*x])^(n+1)/(d*f*(2*n+3)*Sqrt[a+b*Cos[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1))]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b^2*(B*c-A*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)*Sqrt[a+b*Sin[e+f*x]]) + 
  (A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)))/(2*d*(n+1)*(b*c+a*d))*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && 
  NonzeroQ[A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1))] && RationalQ[n] && n<-1


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b^2*(B*c-A*d)*Sin[e+f*x]*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)*Sqrt[a+b*Cos[e+f*x]]) + 
  (A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)))/(2*d*(n+1)*(b*c+a*d))*Int[Sqrt[a+b*Cos[e+f*x]]*(c+d*Cos[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && 
  NonzeroQ[A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1))] && RationalQ[n] && n<-1


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*b*B*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(2*n+3)*Sqrt[a+b*Sin[e+f*x]]) + 
  (A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)))/(b*d*(2*n+3))*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && 
  NonzeroQ[A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1))] && Not[RationalQ[n] && n<-1]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  2*b*B*Sin[e+f*x]*(c+d*Cos[e+f*x])^(n+1)/(d*f*(2*n+3)*Sqrt[a+b*Cos[e+f*x]]) + 
  (A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)))/(b*d*(2*n+3))*Int[Sqrt[a+b*Cos[e+f*x]]*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && 
  NonzeroQ[A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1))] && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b^2*(B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)) - 
  b/(d*(n+1)*(b*c+a*d))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[a*A*d*(m-n-2)-B*(a*c*(m-1)+b*d*(n+1))-(A*b*d*(m+n+1)-B*(b*c*m-a*d*(n+1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>1/2 && n<-1 && 
  IntegerQ[2*m]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b^2*(B*c-A*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)) - 
  b/(d*(n+1)*(b*c+a*d))*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1)*
    Simp[a*A*d*(m-n-2)-B*(a*c*(m-1)+b*d*(n+1))-(A*b*d*(m+n+1)-B*(b*c*m-a*d*(n+1)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>1/2 && n<-1 && 
  IntegerQ[2*m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
    Simp[a*A*d*(m+n+1)+B*(a*c*(m-1)+b*d*(n+1))+(A*b*d*(m+n+1)-B*(b*c*m-a*d*(2*m+n)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>1/2 && 
  Not[RationalQ[n] && n<-1] && IntegerQ[2*m]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b*B*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^n*
    Simp[a*A*d*(m+n+1)+B*(a*c*(m-1)+b*d*(n+1))+(A*b*d*(m+n+1)-B*(b*c*m-a*d*(2*m+n)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>1/2 && 
  Not[RationalQ[n] && n<-1] && IntegerQ[2*m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[A*(a*d*n-b*c*(m+1))-B*(a*c*m+b*d*n)-d*(a*B*(m-n)+A*b*(m+n+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1/2 && n>0 && 
  IntegerQ[2*m]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n-1)*
    Simp[A*(a*d*n-b*c*(m+1))-B*(a*c*m+b*d*n)-d*(a*B*(m-n)+A*b*(m+n+1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1/2 && n>0 && 
  IntegerQ[2*m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b*(A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(a*f*(2*m+1)*(b*c-a*d)) + 
  1/(a*(2*m+1)*(b*c-a*d))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[B*(a*c*m+b*d*(n+1))+A*(b*c*(m+1)-a*d*(2*m+n+2))+d*(A*b-a*B)*(m+n+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1/2 && 
  Not[RationalQ[n] && n>0] && IntegerQ[2*m]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -b*(A*b-a*B)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(a*f*(2*m+1)*(b*c-a*d)) + 
  1/(a*(2*m+1)*(b*c-a*d))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[B*(a*c*m+b*d*(n+1))+A*(b*c*(m+1)-a*d*(2*m+n+2))+d*(A*b-a*B)*(m+n+2)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1/2 && 
  Not[RationalQ[n] && n>0] && IntegerQ[2*m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)*
    Simp[A*b*c*(m+n+1)+B*(a*c*m+b*d*n)+(A*b*d*(m+n+1)+B*(a*d*m+b*c*n))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>0 && 
  (IntegerQ[n] || ZeroQ[m+1/2])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n-1)*
    Simp[A*b*c*(m+n+1)+B*(a*c*m+b*d*n)+(A*b*d*(m+n+1)+B*(a*d*m+b*c*n))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n>0 && 
  (IntegerQ[n] || ZeroQ[m+1/2])


Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  (A*b-a*B)/(b*c-a*d)*Int[1/Sqrt[a+b*Sin[e+f*x]],x] + 
  (B*c-A*d)/(b*c-a*d)*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_])/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])),x_Symbol] :=
  (A*b-a*B)/(b*c-a*d)*Int[1/Sqrt[a+b*Cos[e+f*x]],x] + 
  (B*c-A*d)/(b*c-a*d)*Int[Sqrt[a+b*Cos[e+f*x]]/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[(a+b*Sin[e+f*x])^m,x] - (B*c-A*d)/d*Int[(a+b*Sin[e+f*x])^m/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NonzeroQ[m+1/2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(A_.+B_.*cos[e_.+f_.*x_])/(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[(a+b*Cos[e+f*x])^m,x] - (B*c-A*d)/d*Int[(a+b*Cos[e+f*x])^m/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NonzeroQ[m+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)) + 
  1/(b*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*(a*d*m+b*c*(n+1))-B*(a*c*m+b*d*(n+1))+b*(B*c-A*d)*(m+n+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n<-1 && 
  (IntegerQ[n] || ZeroQ[m+1/2])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(B*c-A*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)) + 
  1/(b*(n+1)*(c^2-d^2))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)*
    Simp[A*(a*d*m+b*c*(n+1))-B*(a*c*m+b*d*(n+1))+b*(B*c-A*d)*(m+n+2)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[n] && n<-1 && 
  (IntegerQ[n] || ZeroQ[m+1/2])


Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  B/b*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  (A*b-a*B)/b*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_])/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  B/b*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]],x] + 
  (A*b-a*B)/b*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] + 
  B/b*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n,x] + 
  B/b*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*(B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[b*(b*c-a*d)*(B*c-A*d)*(m-1)+a*d*(a*A*c+b*B*c-(A*b+a*B)*d)*(n+1)+
      (b*(b*d*(B*c-A*d)+a*(A*c*d+B*(c^2-2*d^2)))*(n+1)-a*(b*c-a*d)*(B*c-A*d)*(n+2))*Sin[e+f*x]+
      b*(d*(A*b*c+a*B*c-a*A*d)*(m+n+1)-b*B*(c^2*m+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>1 && n<-1


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*(B*c-A*d)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^(n+1)*
    Simp[b*(b*c-a*d)*(B*c-A*d)*(m-1)+a*d*(a*A*c+b*B*c-(A*b+a*B)*d)*(n+1)+
      (b*(b*d*(B*c-A*d)+a*(A*c*d+B*(c^2-2*d^2)))*(n+1)-a*(b*c-a*d)*(B*c-A*d)*(n+2))*Cos[e+f*x]+
      b*(d*(A*b*c+a*B*c-a*A*d)*(m+n+1)-b*B*(c^2*m+d^2*(n+1)))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>1 && n<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^n*
    Simp[a^2*A*d*(m+n+1)+b*B*(b*c*(m-1)+a*d*(n+1))+
      (a*d*(2*A*b+a*B)*(m+n+1)-b*B*(a*c-b*d*(m+n)))*Sin[e+f*x]+
      b*(A*b*d*(m+n+1)-B*(b*c*m-a*d*(2*m+n)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>1 && 
  Not[IntegerQ[n] && n>1 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b*B*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Cos[e+f*x])^(m-2)*(c+d*Cos[e+f*x])^n*
    Simp[a^2*A*d*(m+n+1)+b*B*(b*c*(m-1)+a*d*(n+1))+
      (a*d*(2*A*b+a*B)*(m+n+1)-b*B*(a*c-b*d*(m+n)))*Cos[e+f*x]+
      b*(A*b*d*(m+n+1)-B*(b*c*m-a*d*(2*m+n)))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>1 && 
  Not[IntegerQ[n] && n>1 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2*(A*b-a*B)*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) + 
  d/(a^2-b^2)*Int[(A*b-a*B+(a*A-b*B)*Sin[e+f*x])/(Sqrt[a+b*Sin[e+f*x]]*(d*Sin[e+f*x])^(3/2)),x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[a^2-b^2]


Int[(A_.+B_.*cos[e_.+f_.*x_])/((a_+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  -2*(A*b-a*B)*Sin[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Cos[e+f*x]]*Sqrt[d*Cos[e+f*x]]) + 
  d/(a^2-b^2)*Int[(A*b-a*B+(a*A-b*B)*Cos[e+f*x])/(Sqrt[a+b*Cos[e+f*x]]*(d*Cos[e+f*x])^(3/2)),x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[e_.+f_.*x_])/((b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*A*(c-d)*Tan[e+f*x]/(f*b*c^2)*Rt[(c+d)/b,2]*Sqrt[c*(1+Csc[e+f*x])/(c-d)]*Sqrt[c*(1-Csc[e+f*x])/(c+d)]*
    EllipticE[ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f,A,B},x] && NonzeroQ[c^2-d^2] && ZeroQ[A-B] && PosQ[(c+d)/b]


Int[(A_+B_.*cos[e_.+f_.*x_])/((b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  2*A*(c-d)*Cot[e+f*x]/(f*b*c^2)*Rt[(c+d)/b,2]*Sqrt[c*(1+Sec[e+f*x])/(c-d)]*Sqrt[c*(1-Sec[e+f*x])/(c+d)]*
    EllipticE[ArcSin[Sqrt[c+d*Cos[e+f*x]]/Sqrt[b*Cos[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f,A,B},x] && NonzeroQ[c^2-d^2] && ZeroQ[A-B] && PosQ[(c+d)/b]


Int[(A_+B_.*sin[e_.+f_.*x_])/((b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -Sqrt[-b*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]*Int[(A+B*Sin[e+f*x])/((-b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{b,c,d,e,f,A,B},x] && NonzeroQ[c^2-d^2] && ZeroQ[A-B] && NegQ[(c+d)/b]


Int[(A_+B_.*cos[e_.+f_.*x_])/((b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  -Sqrt[-b*Cos[e+f*x]]/Sqrt[b*Cos[e+f*x]]*Int[(A+B*Cos[e+f*x])/((-b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{b,c,d,e,f,A,B},x] && NonzeroQ[c^2-d^2] && ZeroQ[A-B] && NegQ[(c+d)/b]


Int[(A_+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*A*(c-d)*(a+b*Sin[e+f*x])/(f*(b*c-a*d)^2*Rt[(a+b)/(c+d),2]*Cos[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Sin[e+f*x])/((c-d)*(a+b*Sin[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Sin[e+f*x])/((c+d)*(a+b*Sin[e+f*x]))]*
    EllipticE[ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[A-B] && PosQ[(a+b)/(c+d)]


Int[(A_+B_.*cos[e_.+f_.*x_])/((a_+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  2*A*(c-d)*(a+b*Cos[e+f*x])/(f*(b*c-a*d)^2*Rt[(a+b)/(c+d),2]*Sin[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Cos[e+f*x])/((c-d)*(a+b*Cos[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Cos[e+f*x])/((c+d)*(a+b*Cos[e+f*x]))]*
    EllipticE[ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[A-B] && PosQ[(a+b)/(c+d)]


Int[(A_+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-c-d*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]]*Int[(A+B*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[-c-d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[A-B] && NegQ[(a+b)/(c+d)]


Int[(A_+B_.*cos[e_.+f_.*x_])/((a_+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-c-d*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]]*Int[(A+B*Cos[e+f*x])/((a+b*Cos[e+f*x])^(3/2)*Sqrt[-c-d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && ZeroQ[A-B] && NegQ[(a+b)/(c+d)]


Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  (A-B)/(a-b)*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] - 
  (A*b-a*B)/(a-b)*Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NonzeroQ[A-B]


Int[(A_.+B_.*cos[e_.+f_.*x_])/((a_.+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  (A-B)/(a-b)*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]),x] - 
  (A*b-a*B)/(a-b)*Int[(1+Cos[e+f*x])/((a+b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NonzeroQ[A-B]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (B*a-A*b)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[c*(a*A-b*B)*(m+1)+d*n*(A*b-a*B)+(d*(a*A-b*B)*(m+1)-c*(A*b-a*B)*(m+2))*Sin[e+f*x]-d*(A*b-a*B)*(m+n+2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(B*a-A*b)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n-1)*
    Simp[c*(a*A-b*B)*(m+1)+d*n*(A*b-a*B)+(d*(a*A-b*B)*(m+1)-c*(A*b-a*B)*(m+2))*Cos[e+f*x]-d*(A*b-a*B)*(m+n+2)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(A*b^2-a*b*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(1+n)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[(a*A-b*B)*(b*c-a*d)*(m+1)+b*d*(A*b-a*B)*(m+n+2)+
      (A*b-a*B)*(a*d*(m+1)-b*c*(m+2))*Sin[e+f*x]-
      b*d*(A*b-a*B)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  (ZeroQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || ZeroQ[a])])


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (A*b^2-a*b*B)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(1+n)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[(a*A-b*B)*(b*c-a*d)*(m+1)+b*d*(A*b-a*B)*(m+n+2)+
      (A*b-a*B)*(a*d*(m+1)-b*c*(m+2))*Cos[e+f*x]-
      b*d*(A*b-a*B)*(m+n+3)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  (ZeroQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || ZeroQ[a])])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) + 
  1/(m+n+1)*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[a*A*c*(m+n+1)+B*(b*c*m+a*d*n)+
      (B*(a*c+b*d)*(m+n)+A*(b*c+a*d)*(m+n+1))*Sin[e+f*x]+
      (A*b*d*(m+n+1)+B*(a*d*m+b*c*n))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && 0<m<1 && n>-1


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(f*(m+n+1)) + 
  1/(m+n+1)*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n-1)*
    Simp[a*A*c*(m+n+1)+B*(b*c*m+a*d*n)+
      (B*(a*c+b*d)*(m+n)+A*(b*c+a*d)*(m+n+1))*Cos[e+f*x]+
      (A*b*d*(m+n+1)+B*(a*d*m+b*c*n))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && 0<m<1 && n>-1


Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_.+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  (A*b-a*B)/(b*c-a*d)*Int[1/(a+b*Sin[e+f*x]),x] + (B*c-A*d)/(b*c-a*d)*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_])/((a_.+b_.*cos[e_.+f_.*x_])*(c_.+d_.*cos[e_.+f_.*x_])),x_Symbol] :=
  (A*b-a*B)/(b*c-a*d)*Int[1/(a+b*Cos[e+f*x]),x] + (B*c-A*d)/(b*c-a*d)*Int[1/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_+B_.*sin[e_.+f_.*x_])/(Sqrt[sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  4*A/(f*Sqrt[a+b])*EllipticPi[-1,-ArcSin[Cos[e+f*x]/(1+Sin[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,e,f,A,B},x] && PositiveQ[b] && PositiveQ[b^2-a^2] && ZeroQ[A-B]


Int[(A_+B_.*cos[e_.+f_.*x_])/(Sqrt[cos[e_.+f_.*x_]]*Sqrt[a_+b_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  4*A/(f*Sqrt[a+b])*EllipticPi[-1,ArcSin[Sin[e+f*x]/(1+Cos[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,e,f,A,B},x] && PositiveQ[b] && PositiveQ[b^2-a^2] && ZeroQ[A-B]


Int[(A_+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]*Int[(A+B*Sin[e+f*x])/(Sqrt[Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] /;
FreeQ[{a,b,e,f,d,A,B},x] && PositiveQ[b] && PositiveQ[b^2-a^2] && ZeroQ[A-B]


Int[(A_+B_.*cos[e_.+f_.*x_])/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[d_*cos[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[Cos[e+f*x]]/Sqrt[d*Cos[e+f*x]]*Int[(A+B*Cos[e+f*x])/(Sqrt[Cos[e+f*x]]*Sqrt[a+b*Cos[e+f*x]]),x] /;
FreeQ[{a,b,e,f,d,A,B},x] && PositiveQ[b] && PositiveQ[b^2-a^2] && ZeroQ[A-B]


Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  B/d*Int[Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] - 
  (B*c-A*d)/d*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_])/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  B/d*Int[Sqrt[c+d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]],x] - 
  (B*c-A*d)/d*Int[1/(Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(A_.+B_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  B/d*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] - 
  (B*c-A*d)/d*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_.+b_.*cos[e_.+f_.*x_]]*(A_.+B_.*cos[e_.+f_.*x_])/(c_.+d_.*cos[e_.+f_.*x_])^(3/2),x_Symbol] :=
  B/d*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]],x] - 
  (B*c-A*d)/d*Int[Sqrt[a+b*Cos[e+f*x]]/(c+d*Cos[e+f*x])^(3/2),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[(a+b*Sin[e+f*x])^m,x] - (B*c-A*d)/d*Int[(a+b*Sin[e+f*x])^m/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(A_.+B_.*cos[e_.+f_.*x_])/(c_.+d_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[(a+b*Cos[e+f*x])^m,x] - (B*c-A*d)/d*Int[(a+b*Cos[e+f*x])^m/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  Defer[Int][(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+B*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  Defer[Int][(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n*(A+B*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[sin[e_.+f_.*x_]]*(A_+B_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -Sqrt[a+b]/(A*f)*EllipticE[ArcSin[Cos[e+f*x]/(1+Sin[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,e,f,A,B},x] && ZeroQ[B-A] && PositiveQ[b] && PositiveQ[b^2-a^2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/(Sqrt[cos[e_.+f_.*x_]]*(A_+B_.*cos[e_.+f_.*x_])),x_Symbol] :=
  Sqrt[a+b]/(A*f)*EllipticE[ArcSin[Sin[e+f*x]/(1+Cos[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,e,f,A,B},x] && ZeroQ[B-A] && PositiveQ[b] && PositiveQ[b^2-a^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[sin[e_.+f_.*x_]]*(A_+B_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -(a+b)*Sqrt[1+Sin[e+f*x]]*Sqrt[(a+b*Sin[e+f*x])/((a+b)*(1+Sin[e+f*x]))]/(A*f*Sqrt[a+b*Sin[e+f*x]])*
    EllipticE[ArcSin[Cos[e+f*x]/(1+Sin[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,e,f,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/(Sqrt[cos[e_.+f_.*x_]]*(A_+B_.*cos[e_.+f_.*x_])),x_Symbol] :=
  (a+b)*Sqrt[1+Cos[e+f*x]]*Sqrt[(a+b*Cos[e+f*x])/((a+b)*(1+Cos[e+f*x]))]/(A*f*Sqrt[a+b*Cos[e+f*x]])*
    EllipticE[ArcSin[Sin[e+f*x]/(1+Cos[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,e,f,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2]


(* Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[sin[e_.+f_.*x_]]*(A_+B_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -Sqrt[a+b*Sin[e+f*x]]/(A*f*Sqrt[1+Sin[e+f*x]]*Sqrt[(a+b*Sin[e+f*x])/((a+b)*(1+Sin[e+f*x]))])*
    EllipticE[ArcSin[Cos[e+f*x]/(1+Sin[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,e,f,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2] *)


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[d_*sin[e_.+f_.*x_]]*(A_+B_.*sin[e_.+f_.*x_])),x_Symbol] :=
  Sqrt[Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]*Int[Sqrt[a+b*Sin[e+f*x]]/(Sqrt[Sin[e+f*x]]*(A+A*Sin[e+f*x])),x] /;
FreeQ[{a,b,e,f,d,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/(Sqrt[d_*cos[e_.+f_.*x_]]*(A_+B_.*cos[e_.+f_.*x_])),x_Symbol] :=
  Sqrt[Cos[e+f*x]]/Sqrt[d*Cos[e+f*x]]*Int[Sqrt[a+b*Cos[e+f*x]]/(Sqrt[Cos[e+f*x]]*(A+A*Cos[e+f*x])),x] /;
FreeQ[{a,b,e,f,d,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2]


Int[Sqrt[d_.*sin[e_.+f_.*x_]]/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(A_+B_.*sin[e_.+f_.*x_])),x_Symbol] :=
  a*d/(A*(a-b))*Int[1/(Sqrt[d*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] - 
  d/(a-b)*Int[Sqrt[a+b*Sin[e+f*x]]/(Sqrt[d*Sin[e+f*x]]*(A+B*Sin[e+f*x])),x] /;
FreeQ[{a,b,e,f,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]


Int[Sqrt[d_.*cos[e_.+f_.*x_]]/(Sqrt[a_.+b_.*cos[e_.+f_.*x_]]*(A_+B_.*cos[e_.+f_.*x_])),x_Symbol] :=
  a*d/(A*(a-b))*Int[1/(Sqrt[d*Cos[e+f*x]]*Sqrt[a+b*Cos[e+f*x]]),x] - 
  d/(a-b)*Int[Sqrt[a+b*Cos[e+f*x]]/(Sqrt[d*Cos[e+f*x]]*(A+B*Cos[e+f*x])),x] /;
FreeQ[{a,b,e,f,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]


(* ::Subsection::Closed:: *)
(*3.3 (a+b sin)^m (A+B sin+C sin^2)*)


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  1/b^2*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[b*B-a*C+b*C*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  1/b^2*Int[(a+b*Cos[e+f*x])^(m+1)*Simp[b*B-a*C+b*C*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  C/b^2*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[-a+b*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && ZeroQ[A*b^2+a^2*C]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C/b^2*Int[(a+b*Cos[e+f*x])^(m+1)*Simp[-a+b*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && ZeroQ[A*b^2+a^2*C]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b-a*B+b*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*A*(m+1)+m*(b*B-a*C)+b*C*(2*m+1)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<-1 && ZeroQ[a^2-b^2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b-a*B+b*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*Simp[a*A*(m+1)+m*(b*B-a*C)+b*C*(2*m+1)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<-1 && ZeroQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  b*(A+C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*A*(m+1)-a*C*m+b*C*(2*m+1)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[m] && m<-1 && ZeroQ[a^2-b^2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  -b*(A+C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*Simp[a*A*(m+1)-a*C*m+b*C*(2*m+1)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[m] && m<-1 && ZeroQ[a^2-b^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*
    Int[(a+b*Sin[e+f*x])^(m+1)*Simp[b*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<-1 && NonzeroQ[a^2-b^2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*
    Int[(a+b*Cos[e+f*x])^(m+1)*Simp[b*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(m+1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<-1 && NonzeroQ[a^2-b^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*
    Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*b*(A+C)*(m+1)-(A*b^2+a^2*C+b^2*(A+C)*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[m] && m<-1 && NonzeroQ[a^2-b^2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*
    Int[(a+b*Cos[e+f*x])^(m+1)*Simp[a*b*(A+C)*(m+1)-(A*b^2+a^2*C+b^2*(A+C)*(m+1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[m] && m<-1 && NonzeroQ[a^2-b^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[A*b*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && Not[RationalQ[m] && m<-1]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Cos[e+f*x])^m*Simp[A*b*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && Not[RationalQ[m] && m<-1]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[A*b*(m+2)+b*C*(m+1)-a*C*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[A*b^2+a^2*C] && Not[RationalQ[m] && m<-1]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Cos[e+f*x])^m*Simp[A*b*(m+2)+b*C*(m+1)-a*C*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[A*b^2+a^2*C] && Not[RationalQ[m] && m<-1]


(* ::Subsection::Closed:: *)
(*3.4 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2)*)


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(b*c-a*d)*(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*
    Simp[b*(m+1)*((b*B-a*C)*(b*c-a*d)-A*b*(a*c-b*d))+
      (b*B*(a^2*d+b^2*d*(m+1)-a*b*c*(m+2))+(b*c-a*d)*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Sin[e+f*x]-
      b*C*d*(m+1)*(a^2-b^2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (b*c-a*d)*(A*b^2-a*b*B+a^2*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*
    Simp[b*(m+1)*((b*B-a*C)*(b*c-a*d)-A*b*(a*c-b*d))+
      (b*B*(a^2*d+b^2*d*(m+1)-a*b*c*(m+2))+(b*c-a*d)*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Cos[e+f*x]-
      b*C*d*(m+1)*(a^2-b^2)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(b*c-a*d)*(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) + 
  1/(b^2*(m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*
    Simp[b*(m+1)*(a*C*(b*c-a*d)+A*b*(a*c-b*d))-
      ((b*c-a*d)*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Sin[e+f*x]+
      b*C*d*(m+1)*(a^2-b^2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (b*c-a*d)*(A*b^2+a^2*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) + 
  1/(b^2*(m+1)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*
    Simp[b*(m+1)*(a*C*(b*c-a*d)+A*b*(a*c-b*d))-
      ((b*c-a*d)*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Cos[e+f*x]+
      b*C*d*(m+1)*(a^2-b^2)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*d*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[(a+b*Sin[e+f*x])^m*
    Simp[a*C*d+A*b*c*(m+3)+b*(B*c*(m+3)+d*(C*(m+2)+A*(m+3)))*Sin[e+f*x]-(2*a*C*d-b*(c*C+B*d)*(m+3))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*d*Sin[e+f*x]*Cos[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[(a+b*Cos[e+f*x])^m*
    Simp[a*C*d+A*b*c*(m+3)+b*(B*c*(m+3)+d*(C*(m+2)+A*(m+3)))*Cos[e+f*x]-(2*a*C*d-b*(c*C+B*d)*(m+3))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*d*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[(a+b*Sin[e+f*x])^m*
    Simp[a*C*d+A*b*c*(m+3)+b*d*(C*(m+2)+A*(m+3))*Sin[e+f*x]-(2*a*C*d-b*c*C*(m+3))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*d*Sin[e+f*x]*Cos[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[(a+b*Cos[e+f*x])^m*
    Simp[a*C*d+A*b*c*(m+3)+b*d*(C*(m+2)+A*(m+3))*Cos[e+f*x]-(2*a*C*d-b*c*C*(m+3))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A-b*B+a*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))+B*(b*c*m+a*d*(n+1))-C*(a*c*m+b*d*(n+1))+
      (d*(a*A-b*B)*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && 
  (RationalQ[m] && m<-1/2 || ZeroQ[m+n+2] && NonzeroQ[2*m+1])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A-b*B+a*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))+B*(b*c*m+a*d*(n+1))-C*(a*c*m+b*d*(n+1))+
      (d*(a*A-b*B)*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && 
  (RationalQ[m] && m<-1/2 || ZeroQ[m+n+2] && NonzeroQ[2*m+1])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A+C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))-C*(a*c*m+b*d*(n+1))+
      (a*A*d*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && 
  (RationalQ[m] && m<-1/2 || ZeroQ[m+n+2] && NonzeroQ[2*m+1])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A+C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))-C*(a*c*m+b*d*(n+1))+
      (a*A*d*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && 
  (RationalQ[m] && m<-1/2 || ZeroQ[m+n+2] && NonzeroQ[2*m+1])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+3)*Sqrt[c+d*Sin[e+f*x]]) + 
  Int[(a+b*Sin[e+f*x])^m*Simp[A+C+B*Sin[e+f*x],x]/Sqrt[c+d*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2)/Sqrt[c_.+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  2*C*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(2*m+3)*Sqrt[c+d*Cos[e+f*x]]) + 
  Int[(a+b*Cos[e+f*x])^m*Simp[A+C+B*Cos[e+f*x],x]/Sqrt[c+d*Cos[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2)/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+3)*Sqrt[c+d*Sin[e+f*x]]) + 
  (A+C)*Int[(a+b*Sin[e+f*x])^m/Sqrt[c+d*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(A_.+C_.*cos[e_.+f_.*x_]^2)/Sqrt[c_.+d_.*cos[e_.+f_.*x_]],x_Symbol] :=
  2*C*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)/(b*f*(2*m+3)*Sqrt[c+d*Cos[e+f*x]]) + 
  (A+C)*Int[(a+b*Cos[e+f*x])^m/Sqrt[c+d*Cos[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+(C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+(C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+C*(a*d*m-b*c*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+C*(a*d*m-b*c*(m+1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A-b*B+a*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))+B*(b*c*m+a*d*(n+1))-C*(a*c*m+b*d*(n+1))+
      (d*(a*A-b*B)*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A-b*B+a*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))+B*(b*c*m+a*d*(n+1))-C*(a*c*m+b*d*(n+1))+
      (d*(a*A-b*B)*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A+C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))-C*(a*c*m+b*d*(n+1))+
      (a*A*d*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A+C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))-C*(a*c*m+b*d*(n+1))+
      (a*A*d*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C-B*c*d+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(b*d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*d*(a*d*m+b*c*(n+1))+(c*C-B*d)*(a*c*m+b*d*(n+1))+b*(d*(B*c-A*d)*(m+n+2)-C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  (RationalQ[n] && n<-1 || ZeroQ[m+n+2])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (c^2*C-B*c*d+A*d^2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(b*d*(n+1)*(c^2-d^2))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)*
    Simp[A*d*(a*d*m+b*c*(n+1))+(c*C-B*d)*(a*c*m+b*d*(n+1))+b*(d*(B*c-A*d)*(m+n+2)-C*(c^2*(m+1)+d^2*(n+1)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  (RationalQ[n] && n<-1 || ZeroQ[m+n+2])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(b*d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*d*(a*d*m+b*c*(n+1))+c*C*(a*c*m+b*d*(n+1))-b*(A*d^2*(m+n+2)+C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  (RationalQ[n] && n<-1 || ZeroQ[m+n+2])


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (c^2*C+A*d^2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(b*d*(n+1)*(c^2-d^2))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)*
    Simp[A*d*(a*d*m+b*c*(n+1))+c*C*(a*c*m+b*d*(n+1))-b*(A*d^2*(m+n+2)+C*(c^2*(m+1)+d^2*(n+1)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  (RationalQ[n] && n<-1 || ZeroQ[m+n+2])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+(C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+(C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+C*(a*d*m-b*c*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+C*(a*d*m-b*c*(m+1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NonzeroQ[m+n+2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C-B*c*d+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m+a*c*(n+1))+(c*C-B*d)*(b*c*m+a*d*(n+1)) - 
      (d*(A*(a*d*(n+2)-b*c*(n+1))+B*(b*d*(n+1)-a*c*(n+2)))-C*(b*c*d*(n+1)-a*(c^2+d^2*(n+1))))*Sin[e+f*x] + 
      b*(d*(B*c-A*d)*(m+n+2)-C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (c^2*C-B*c*d+A*d^2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m+a*c*(n+1))+(c*C-B*d)*(b*c*m+a*d*(n+1)) - 
      (d*(A*(a*d*(n+2)-b*c*(n+1))+B*(b*d*(n+1)-a*c*(n+2)))-C*(b*c*d*(n+1)-a*(c^2+d^2*(n+1))))*Cos[e+f*x] + 
      b*(d*(B*c-A*d)*(m+n+2)-C*(c^2*(m+1)+d^2*(n+1)))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m+a*c*(n+1))+c*C*(b*c*m+a*d*(n+1)) - 
      (A*d*(a*d*(n+2)-b*c*(n+1))-C*(b*c*d*(n+1)-a*(c^2+d^2*(n+1))))*Sin[e+f*x] - 
      b*(A*d^2*(m+n+2)+C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (c^2*C+A*d^2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m+a*c*(n+1))+c*C*(b*c*m+a*d*(n+1)) - 
      (A*d*(a*d*(n+2)-b*c*(n+1))-C*(b*c*d*(n+1)-a*(c^2+d^2*(n+1))))*Cos[e+f*x] - 
      b*(A*d^2*(m+n+2)+C*(c^2*(m+1)+d^2*(n+1)))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(d*(m+n+2))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
    Simp[a*A*d*(m+n+2)+C*(b*c*m+a*d*(n+1))+
      (d*(A*b+a*B)*(m+n+2)-C*(a*c-b*d*(m+n+1)))*Sin[e+f*x]+
      (C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(d*(m+n+2))*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^n*
    Simp[a*A*d*(m+n+2)+C*(b*c*m+a*d*(n+1))+
      (d*(A*b+a*B)*(m+n+2)-C*(a*c-b*d*(m+n+1)))*Cos[e+f*x]+
      (C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(d*(m+n+2))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
    Simp[a*A*d*(m+n+2)+C*(b*c*m+a*d*(n+1))+(A*b*d*(m+n+2)-C*(a*c-b*d*(m+n+1)))*Sin[e+f*x]+C*(a*d*m-b*c*(m+1))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sin[e+f*x]*(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(d*(m+n+2))*Int[(a+b*Cos[e+f*x])^(m-1)*(c+d*Cos[e+f*x])^n*
    Simp[a*A*d*(m+n+2)+C*(b*c*m+a*d*(n+1))+(A*b*d*(m+n+2)-C*(a*c-b*d*(m+n+1)))*Cos[e+f*x]+C*(a*d*m-b*c*(m+1))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || ZeroQ[a] && NonzeroQ[c])]


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  C/(b*d)*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] + 
  1/b*Int[(A*b+(b*B-a*C)*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2)/((a_+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  C/(b*d)*Int[Sqrt[d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]],x] + 
  1/b*Int[(A*b+(b*B-a*C)*Cos[e+f*x])/((a+b*Cos[e+f*x])^(3/2)*Sqrt[d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  C/(b*d)*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] + 
  1/b*Int[(A*b-a*C*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+C_.*cos[e_.+f_.*x_]^2)/((a_+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  C/(b*d)*Int[Sqrt[d*Cos[e+f*x]]/Sqrt[a+b*Cos[e+f*x]],x] + 
  1/b*Int[(A*b-a*C*Cos[e+f*x])/((a+b*Cos[e+f*x])^(3/2)*Sqrt[d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  C/b^2*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  1/b^2*Int[(A*b^2-a^2*C+b*(b*B-2*a*C)*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2)/((a_.+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  C/b^2*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]],x] + 
  1/b^2*Int[(A*b^2-a^2*C+b*(b*B-2*a*C)*Cos[e+f*x])/((a+b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  C/b^2*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  1/b^2*Int[(A*b^2-a^2*C-2*a*b*C*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+C_.*cos[e_.+f_.*x_]^2)/((a_.+b_.*cos[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  C/b^2*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[c+d*Cos[e+f*x]],x] + 
  1/b^2*Int[(A*b^2-a^2*C-2*a*b*C*Cos[e+f*x])/((a+b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[(m+1)*(b*c-a*d)*(a*A-b*B+a*C)+d*(A*b^2-a*b*B+a^2*C)*(m+n+2) - 
      (c*(A*b^2-a*b*B+a^2*C)+(m+1)*(b*c-a*d)*(A*b-a*B+b*C))*Sin[e+f*x] - 
      d*(A*b^2-a*b*B+a^2*C)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 &&
  (ZeroQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || ZeroQ[a])])


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[(m+1)*(b*c-a*d)*(a*A-b*B+a*C)+d*(A*b^2-a*b*B+a^2*C)*(m+n+2) - 
      (c*(A*b^2-a*b*B+a^2*C)+(m+1)*(b*c-a*d)*(A*b-a*B+b*C))*Cos[e+f*x] - 
      d*(A*b^2-a*b*B+a^2*C)*(m+n+3)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 &&
  (ZeroQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || ZeroQ[a])])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[a*(m+1)*(b*c-a*d)*(A+C)+d*(A*b^2+a^2*C)*(m+n+2) - 
      (c*(A*b^2+a^2*C)+b*(m+1)*(b*c-a*d)*(A+C))*Sin[e+f*x] - 
      d*(A*b^2+a^2*C)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  (ZeroQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || ZeroQ[a])])


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*
    Simp[a*(m+1)*(b*c-a*d)*(A+C)+d*(A*b^2+a^2*C)*(m+n+2) - 
      (c*(A*b^2+a^2*C)+b*(m+1)*(b*c-a*d)*(A+C))*Cos[e+f*x] - 
      d*(A*b^2+a^2*C)*(m+n+3)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  (ZeroQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || ZeroQ[a])])


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  C*x/(b*d) + 
  (A*b^2-a*b*B+a^2*C)/(b*(b*c-a*d))*Int[1/(a+b*Sin[e+f*x]),x] - 
  (c^2*C-B*c*d+A*d^2)/(d*(b*c-a*d))*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2)/((a_+b_.*cos[e_.+f_.*x_])*(c_.+d_.*cos[e_.+f_.*x_])),x_Symbol] :=
  C*x/(b*d) + 
  (A*b^2-a*b*B+a^2*C)/(b*(b*c-a*d))*Int[1/(a+b*Cos[e+f*x]),x] - 
  (c^2*C-B*c*d+A*d^2)/(d*(b*c-a*d))*Int[1/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  C*x/(b*d) + 
  (A*b^2+a^2*C)/(b*(b*c-a*d))*Int[1/(a+b*Sin[e+f*x]),x] - 
  (c^2*C+A*d^2)/(d*(b*c-a*d))*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+C_.*cos[e_.+f_.*x_]^2)/((a_+b_.*cos[e_.+f_.*x_])*(c_.+d_.*cos[e_.+f_.*x_])),x_Symbol] :=
  C*x/(b*d) + 
  (A*b^2+a^2*C)/(b*(b*c-a*d))*Int[1/(a+b*Cos[e+f*x]),x] - 
  (c^2*C+A*d^2)/(d*(b*c-a*d))*Int[1/(c+d*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  C/(b*d)*Int[Sqrt[a+b*Sin[e+f*x]],x] - 
  1/(b*d)*Int[Simp[a*c*C-A*b*d+(b*c*C-b*B*d+a*C*d)*Sin[e+f*x],x]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])),x_Symbol] :=
  C/(b*d)*Int[Sqrt[a+b*Cos[e+f*x]],x] - 
  1/(b*d)*Int[Simp[a*c*C-A*b*d+(b*c*C-b*B*d+a*C*d)*Cos[e+f*x],x]/(Sqrt[a+b*Cos[e+f*x]]*(c+d*Cos[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  C/(b*d)*Int[Sqrt[a+b*Sin[e+f*x]],x] - 
  1/(b*d)*Int[Simp[a*c*C-A*b*d+(b*c*C+a*C*d)*Sin[e+f*x],x]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+C_.*cos[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*cos[e_.+f_.*x_]]*(c_.+d_.*cos[e_.+f_.*x_])),x_Symbol] :=
  C/(b*d)*Int[Sqrt[a+b*Cos[e+f*x]],x] - 
  1/(b*d)*Int[Simp[a*c*C-A*b*d+(b*c*C+a*C*d)*Cos[e+f*x],x]/(Sqrt[a+b*Cos[e+f*x]]*(c+d*Cos[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -C*Cos[e+f*x]*Sqrt[c+d*Sin[e+f*x]]/(d*f*Sqrt[a+b*Sin[e+f*x]]) + 
  1/(2*d)*Int[1/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]])*
    Simp[2*a*A*d-C*(b*c-a*d)-2*(a*c*C-d*(A*b+a*B))*Sin[e+f*x]+(2*b*B*d-C*(b*c+a*d))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*cos[e_.+f_.*x_]]*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  C*Sin[e+f*x]*Sqrt[c+d*Cos[e+f*x]]/(d*f*Sqrt[a+b*Cos[e+f*x]]) + 
  1/(2*d)*Int[1/((a+b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]])*
    Simp[2*a*A*d-C*(b*c-a*d)-2*(a*c*C-d*(A*b+a*B))*Cos[e+f*x]+(2*b*B*d-C*(b*c+a*d))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -C*Cos[e+f*x]*Sqrt[c+d*Sin[e+f*x]]/(d*f*Sqrt[a+b*Sin[e+f*x]]) + 
  1/(2*d)*Int[1/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]])*
    Simp[2*a*A*d-C*(b*c-a*d)-2*(a*c*C-A*b*d)*Sin[e+f*x]-C*(b*c+a*d)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(A_.+C_.*cos[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*cos[e_.+f_.*x_]]*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  C*Sin[e+f*x]*Sqrt[c+d*Cos[e+f*x]]/(d*f*Sqrt[a+b*Cos[e+f*x]]) + 
  1/(2*d)*Int[1/((a+b*Cos[e+f*x])^(3/2)*Sqrt[c+d*Cos[e+f*x]])*
    Simp[2*a*A*d-C*(b*c-a*d)-2*(a*c*C-A*b*d)*Cos[e+f*x]-C*(b*c+a*d)*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+B*Sin[e+f*x]+C*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n*(A+B*Cos[e+f*x]+C*Cos[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+C*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n*(A+C*Cos[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


(* ::Subsection::Closed:: *)
(*4.1 (g cos)^p (a+b sin)^m*)


Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  1/(b^p*f)*Subst[Int[(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && ZeroQ[a^2-b^2] && (p>=-1 || Not[IntegerQ[m+1/2] && ZeroQ[a^2-b^2]])


Int[sin[e_.+f_.*x_]^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_.,x_Symbol] :=
  -1/(b^p*f)*Subst[Int[(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2),x],x,b*Cos[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && ZeroQ[a^2-b^2] && (p>=-1 || Not[IntegerQ[m+1/2] && ZeroQ[a^2-b^2]])


Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  1/(b^p*f)*Subst[Int[(a+x)^m*(b^2-x^2)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && NonzeroQ[a^2-b^2]


Int[sin[e_.+f_.*x_]^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_.,x_Symbol] :=
  -1/(b^p*f)*Subst[Int[(a+x)^m*(b^2-x^2)^((p-1)/2),x],x,b*Cos[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && NonzeroQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)/(f*g*(p+1)) + a*Int[(g*Cos[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g,p},x] && Not[IntegerQ[(p-1)/2]] && (IntegerQ[2*p] || NonzeroQ[a^2-b^2])


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  b*(g*Sin[e+f*x])^(p+1)/(f*g*(p+1)) + a*Int[(g*Sin[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g,p},x] && Not[IntegerQ[(p-1)/2]] && (IntegerQ[2*p] || NonzeroQ[a^2-b^2])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*m) /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && ZeroQ[Simplify[m+p+1]]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(a*f*g*m) /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && ZeroQ[Simplify[m+p+1]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*Simplify[2*m+p+1]) + 
  Simplify[m+p+1]/(a*Simplify[2*m+p+1])*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && NegativeIntegerQ[Simplify[m+p+1]] && NonzeroQ[2*m+p+1] && Not[PositiveIntegerQ[m]]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(a*f*g*Simplify[2*m+p+1]) + 
  Simplify[m+p+1]/(a*Simplify[2*m+p+1])*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && NegativeIntegerQ[Simplify[m+p+1]] && NonzeroQ[2*m+p+1] && Not[PositiveIntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m-1)) /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && ZeroQ[2*m+p-1] && NonzeroQ[m-1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m-1)/(f*g*(m-1)) /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && ZeroQ[2*m+p-1] && NonzeroQ[m-1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) + 
  a*(2*m+p-1)/(m+p)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && PositiveIntegerQ[Simplify[(2*m+p-1)/2]] && NonzeroQ[m+p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m-1)/(f*g*(m+p)) + 
  a*(2*m+p-1)/(m+p)*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && PositiveIntegerQ[Simplify[(2*m+p-1)/2]] && NonzeroQ[m+p]


Int[(g_.*cos[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)/(a*f*g*(p-1)*(a+b*Sin[e+f*x])) + 
  p/(a*(p-1))*Int[(g*Cos[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[p] && p<0


Int[(g_.*sin[e_.+f_.*x_])^p_/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -b*(g*Sin[e+f*x])^(p+1)/(a*f*g*(p-1)*(a+b*Cos[e+f*x])) + 
  p/(a*(p-1))*Int[(g*Sin[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[p] && p<0


Int[(g_.*cos[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g^2/a*Int[(g*Cos[e+f*x])^(p-2),x] - g^2/b*Int[Sin[e+f*x]*(g*Cos[e+f*x])^(p-2),x] /;
FreeQ[{a,b,e,f,g,p},x] && ZeroQ[a^2-b^2] && Not[RationalQ[p] && p<0]


Int[(g_.*sin[e_.+f_.*x_])^p_/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  g^2/a*Int[(g*Sin[e+f*x])^(p-2),x] - g^2/b*Int[Cos[e+f*x]*(g*Sin[e+f*x])^(p-2),x] /;
FreeQ[{a,b,e,f,g,p},x] && ZeroQ[a^2-b^2] && Not[RationalQ[p] && p<0]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(p+1)) + 
  a*(m+p+1)/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && m>0 && p<=-2*m && IntegersQ[m+1/2,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(a*f*g*(p+1)) + 
  a*(m+p+1)/(g^2*(p+1))*Int[(g*Sin[e+f*x])^(p+2)*(a+b*Cos[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && m>0 && p<=-2*m && IntegersQ[m+1/2,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -2*b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(p+1)) + 
  b^2*(2*m+p-1)/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-2),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && m>1 && p<-1 && IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  2*b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m-1)/(f*g*(p+1)) + 
  b^2*(2*m+p-1)/(g^2*(p+1))*Int[(g*Sin[e+f*x])^(p+2)*(a+b*Cos[e+f*x])^(m-2),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && m>1 && p<-1 && IntegersQ[2*m,2*p]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[g_.*cos[e_.+f_.*x_]],x_Symbol] :=
  a*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x])*Int[Sqrt[1+Cos[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] + 
  b*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x])*Int[Sin[e+f*x]/(Sqrt[g*Cos[e+f*x]]*Sqrt[1+Cos[e+f*x]]),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[e_.+f_.*x_]]/Sqrt[g_.*sin[e_.+f_.*x_]],x_Symbol] :=
  a*Sqrt[1+Sin[e+f*x]]*Sqrt[a+b*Cos[e+f*x]]/(a+a*Sin[e+f*x]+b*Cos[e+f*x])*Int[Sqrt[1+Sin[e+f*x]]/Sqrt[g*Sin[e+f*x]],x] + 
  b*Sqrt[1+Sin[e+f*x]]*Sqrt[a+b*Cos[e+f*x]]/(a+a*Sin[e+f*x]+b*Cos[e+f*x])*Int[Cos[e+f*x]/(Sqrt[g*Sin[e+f*x]]*Sqrt[1+Sin[e+f*x]]),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) + 
  a*(2*m+p-1)/(m+p)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>0 && NonzeroQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m-1)/(f*g*(m+p)) + 
  a*(2*m+p-1)/(m+p)*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>0 && NonzeroQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+p)) + 
  g^2*(p-1)/(a*(m+p))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && (m>-2 || ZeroQ[2*m+p+1] || m==-2 && IntegerQ[p]) && 
  NonzeroQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -g*(g*Sin[e+f*x])^(p-1)*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+p)) + 
  g^2*(p-1)/(a*(m+p))*Int[(g*Sin[e+f*x])^(p-2)*(a+b*Cos[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && (m>-2 || ZeroQ[2*m+p+1] || m==-2 && IntegerQ[p]) && 
  NonzeroQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  2*g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+p+1)) + 
  g^2*(p-1)/(b^2*(2*m+p+1))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+2),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && m<=-2 && p>1 && NonzeroQ[2*m+p+1] && Not[NegativeIntegerQ[m+p+1]] && 
  IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -2*g*(g*Sin[e+f*x])^(p-1)*(a+b*Cos[e+f*x])^(m+1)/(b*f*(2*m+p+1)) + 
  g^2*(p-1)/(b^2*(2*m+p+1))*Int[(g*Sin[e+f*x])^(p-2)*(a+b*Cos[e+f*x])^(m+2),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && m<=-2 && p>1 && NonzeroQ[2*m+p+1] && Not[NegativeIntegerQ[m+p+1]] && 
  IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(2*m+p+1)) + 
  (m+p+1)/(a*(2*m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1 && NonzeroQ[2*m+p+1] && IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(a*f*g*(2*m+p+1)) + 
  (m+p+1)/(a*(2*m+p+1))*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1 && NonzeroQ[2*m+p+1] && IntegersQ[2*m,2*p]


Int[Sqrt[g_.*cos[e_.+f_.*x_]]/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  g*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x])*Int[Sqrt[1+Cos[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] - 
  g*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(b+b*Cos[e+f*x]+a*Sin[e+f*x])*Int[Sin[e+f*x]/(Sqrt[g*Cos[e+f*x]]*Sqrt[1+Cos[e+f*x]]),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2]


Int[Sqrt[g_.*sin[e_.+f_.*x_]]/Sqrt[a_+b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  g*Sqrt[1+Sin[e+f*x]]*Sqrt[a+b*Cos[e+f*x]]/(a+a*Sin[e+f*x]+b*Cos[e+f*x])*Int[Sqrt[1+Sin[e+f*x]]/Sqrt[g*Sin[e+f*x]],x] - 
  g*Sqrt[1+Sin[e+f*x]]*Sqrt[a+b*Cos[e+f*x]]/(b+b*Sin[e+f*x]+a*Cos[e+f*x])*Int[Cos[e+f*x]/(Sqrt[g*Sin[e+f*x]]*Sqrt[1+Sin[e+f*x]]),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  g*Sqrt[g*Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(b*f) + 
  g^2/(2*a)*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2]


Int[(g_.*sin[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  -g*Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Cos[e+f*x]]/(b*f) + 
  g^2/(2*a)*Int[Sqrt[a+b*Cos[e+f*x]]/Sqrt[g*Sin[e+f*x]],x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*b*(g*Cos[e+f*x])^(p+1)/(f*g*(2*p-1)*(a+b*Sin[e+f*x])^(3/2)) + 
  2*a*(p-2)/(2*p-1)*Int[(g*Cos[e+f*x])^p/(a+b*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[p] && p>2 && IntegerQ[2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_/Sqrt[a_+b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  2*b*(g*Sin[e+f*x])^(p+1)/(f*g*(2*p-1)*(a+b*Cos[e+f*x])^(3/2)) + 
  2*a*(p-2)/(2*p-1)*Int[(g*Sin[e+f*x])^p/(a+b*Cos[e+f*x])^(3/2),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[p] && p>2 && IntegerQ[2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)/(a*f*g*(p+1)*Sqrt[a+b*Sin[e+f*x]]) + 
  a*(2*p+1)/(2*g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)/(a+b*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[p] && p<-1 && IntegerQ[2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_/Sqrt[a_+b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  b*(g*Sin[e+f*x])^(p+1)/(a*f*g*(p+1)*Sqrt[a+b*Cos[e+f*x]]) + 
  a*(2*p+1)/(2*g^2*(p+1))*Int[(g*Sin[e+f*x])^(p+2)/(a+b*Cos[e+f*x])^(3/2),x] /;
FreeQ[{a,b,e,f,g},x] && ZeroQ[a^2-b^2] && RationalQ[p] && p<-1 && IntegerQ[2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  -2^((2*m+p+1)/2)*a^(m+1)*(g*Cos[e+f*x])^(p+1)/(b*f*g*(p+1)*((a+b*Sin[e+f*x])/a)^((p+1)/2))*
    Hypergeometric2F1[(p+1)/2,-(2*m+p-1)/2,(p+3)/2,(a-b*Sin[e+f*x])/(2*a)] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[(p-1)/2]] && Not[NegativeIntegerQ[m+p]] && 
  Not[PositiveIntegerQ[Simplify[(2*m+p+1)/2]]] && IntegerQ[m]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  2^((2*m+p+1)/2)*a^(m+1)*(g*Sin[e+f*x])^(p+1)/(b*f*g*(p+1)*((a+b*Cos[e+f*x])/a)^((p+1)/2))*
    Hypergeometric2F1[(p+1)/2,-(2*m+p-1)/2,(p+3)/2,(a-b*Cos[e+f*x])/(2*a)] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[(p-1)/2]] && Not[NegativeIntegerQ[m+p]] && 
  Not[PositiveIntegerQ[Simplify[(2*m+p+1)/2]]] && IntegerQ[m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -a*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(b*f*g*(p+1)*((a+b*Sin[e+f*x])/(2*a))^((2*m+p+1)/2))*
    Hypergeometric2F1[(p+1)/2,-(2*m+p-1)/2,(p+3)/2,(a-b*Sin[e+f*x])/(2*a)] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[(p-1)/2]] && Not[NegativeIntegerQ[m+p]] && 
  Not[PositiveIntegerQ[Simplify[(2*m+p+1)/2]]] && Not[IntegerQ[m]]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  a*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(b*f*g*(p+1)*((a+b*Cos[e+f*x])/(2*a))^((2*m+p+1)/2))*
    Hypergeometric2F1[(p+1)/2,-(2*m+p-1)/2,(p+3)/2,(a-b*Cos[e+f*x])/(2*a)] /;
FreeQ[{a,b,e,f,g,m,p},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[(p-1)/2]] && Not[NegativeIntegerQ[m+p]] && 
  Not[PositiveIntegerQ[Simplify[(2*m+p+1)/2]]] && Not[IntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a*Int[(g*Cos[e+f*x])^p,x] + b*Int[Sin[e+f*x]*(g*Cos[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g,p},x]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  a*Int[(g*Sin[e+f*x])^p,x] + b*Int[Cos[e+f*x]*(g*Sin[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g,p},x]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*Sin[e+f*x]/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1)*(a*(p+2)+b*(m+p+2)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && 0<m<1 && p<-1 && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  (g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m*Cos[e+f*x]/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Sin[e+f*x])^(p+2)*(a+b*Cos[e+f*x])^(m-1)*(a*(p+2)+b*(m+p+2)*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && 0<m<1 && p<-1 && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(b+a*Sin[e+f*x])/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-2)*(b^2*(m-1)+a^2*(p+2)+a*b*(m+p+1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && m>1 && p<-1 && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  (g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m-1)*(b+a*Cos[e+f*x])/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Sin[e+f*x])^(p+2)*(a+b*Cos[e+f*x])^(m-2)*(b^2*(m-1)+a^2*(p+2)+a*b*(m+p+1)*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && m>1 && p<-1 && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) + 
  1/(m+p)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-2)*(b^2*(m-1)+a^2*(m+p)+a*b*(2*m+p-1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,p},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && NonzeroQ[m+p] && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m-1)/(f*g*(m+p)) + 
  1/(m+p)*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m-2)*(b^2*(m-1)+a^2*(m+p)+a*b*(2*m+p-1)*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,p},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && NonzeroQ[m+p] && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)) + 
  g^2*(p-1)/(b*(m+1))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1)*Sin[e+f*x],x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -g*(g*Sin[e+f*x])^(p-1)*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+1)) + 
  g^2*(p-1)/(b*(m+1))*Int[(g*Sin[e+f*x])^(p-2)*(a+b*Cos[e+f*x])^(m+1)*Cos[e+f*x],x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a^2-b^2)*(m+1)) + 
  1/((a^2-b^2)*(m+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(a*(m+1)-b*(m+p+2)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,p},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m+1)/(f*g*(a^2-b^2)*(m+1)) + 
  1/((a^2-b^2)*(m+1))*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m+1)*(a*(m+1)-b*(m+p+2)*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,p},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+p)) + 
  g^2*(p-1)/(b*(m+p))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^m*(b+a*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p>1 && NonzeroQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -g*(g*Sin[e+f*x])^(p-1)*(a+b*Cos[e+f*x])^(m+1)/(b*f*(m+p)) + 
  g^2*(p-1)/(b*(m+p))*Int[(g*Sin[e+f*x])^(p-2)*(a+b*Cos[e+f*x])^m*(b+a*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p>1 && NonzeroQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)*(b-a*Sin[e+f*x])/(f*g*(a^2-b^2)*(p+1)) + 
  1/(g^2*(a^2-b^2)*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m*(a^2*(p+2)-b^2*(m+p+2)+a*b*(m+p+3)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1 && IntegersQ[2*m,2*p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m+1)*(b-a*Cos[e+f*x])/(f*g*(a^2-b^2)*(p+1)) + 
  1/(g^2*(a^2-b^2)*(p+1))*Int[(g*Sin[e+f*x])^(p+2)*(a+b*Cos[e+f*x])^m*(a^2*(p+2)-b^2*(m+p+2)+a*b*(m+p+3)*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1 && IntegersQ[2*m,2*p]


Int[Sqrt[g_.*cos[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  ArcTan[Rt[b/g,2]*Sqrt[g*Cos[e+f*x]]/Rt[-a^2+b^2,4]]/(f*Rt[b/g,2]*Rt[-a^2+b^2,4]) - 
  ArcTanh[Rt[b/g,2]*Sqrt[g*Cos[e+f*x]]/Rt[-a^2+b^2,4]]/(f*Rt[b/g,2]*Rt[-a^2+b^2,4]) + 
  a*Rt[g,2]*Rt[-b^2/(a^2-b^2),2]*Sqrt[Sin[e+f*x]^2]/(b^2*f*Sin[e+f*x])*
    (EllipticPi[-Rt[-b^2/(a^2-b^2),2],-ArcSin[Sqrt[g*Cos[e+f*x]]/Rt[g,2]],-1] - 
     EllipticPi[Rt[-b^2/(a^2-b^2),2],-ArcSin[Sqrt[g*Cos[e+f*x]]/Rt[g,2]],-1]) /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[g_.*sin[e_.+f_.*x_]]/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -ArcTan[Rt[b/g,2]*Sqrt[g*Sin[e+f*x]]/Rt[-a^2+b^2,4]]/(f*Rt[b/g,2]*Rt[-a^2+b^2,4]) + 
  ArcTanh[Rt[b/g,2]*Sqrt[g*Sin[e+f*x]]/Rt[-a^2+b^2,4]]/(f*Rt[b/g,2]*Rt[-a^2+b^2,4]) - 
  a*Rt[g,2]*Rt[-b^2/(a^2-b^2),2]*Sqrt[Cos[e+f*x]^2]/(b^2*f*Cos[e+f*x])*
    (EllipticPi[-Rt[-b^2/(a^2-b^2),2],-ArcSin[Sqrt[g*Sin[e+f*x]]/Rt[g,2]],-1] - 
     EllipticPi[Rt[-b^2/(a^2-b^2),2],-ArcSin[Sqrt[g*Sin[e+f*x]]/Rt[g,2]],-1]) /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[g_.*cos[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -Rt[b/g,2]*ArcTan[Rt[b/g,2]*Sqrt[g*Cos[e+f*x]]/Rt[-a^2+b^2,4]]/(f*Rt[-a^2+b^2,4]^3) - 
  Rt[b/g,2]*ArcTanh[Rt[b/g,2]*Sqrt[g*Cos[e+f*x]]/Rt[-a^2+b^2,4]]/(f*Rt[-a^2+b^2,4]^3) + 
  a*Sqrt[Sin[e+f*x]^2]/(f*Rt[g,2]*(a^2-b^2)*Sin[e+f*x])*
    (EllipticPi[-Rt[-b^2/(a^2-b^2),2],-ArcSin[Sqrt[g*Cos[e+f*x]]/Rt[g,2]],-1] + 
     EllipticPi[Rt[-b^2/(a^2-b^2),2],-ArcSin[Sqrt[g*Cos[e+f*x]]/Rt[g,2]],-1]) /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[g_.*sin[e_.+f_.*x_]]*(a_+b_.*cos[e_.+f_.*x_])),x_Symbol] :=
  Rt[b/g,2]*ArcTan[Rt[b/g,2]*Sqrt[g*Sin[e+f*x]]/Rt[-a^2+b^2,4]]/(f*Rt[-a^2+b^2,4]^3) + 
  Rt[b/g,2]*ArcTanh[Rt[b/g,2]*Sqrt[g*Sin[e+f*x]]/Rt[-a^2+b^2,4]]/(f*Rt[-a^2+b^2,4]^3) - 
  a*Sqrt[Cos[e+f*x]^2]/(f*Rt[g,2]*(a^2-b^2)*Cos[e+f*x])*
    (EllipticPi[-Rt[-b^2/(a^2-b^2),2],-ArcSin[Sqrt[g*Sin[e+f*x]]/Rt[g,2]],-1] + 
     EllipticPi[Rt[-b^2/(a^2-b^2),2],-ArcSin[Sqrt[g*Sin[e+f*x]]/Rt[g,2]],-1]) /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[g_.*cos[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  -4*g*(1-Sin[e+f*x])/(3*f*(a+b)*Sqrt[g*Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]])*((a+b)*(1+Sin[e+f*x])/(2*(a+b*Sin[e+f*x])))^(1/4)*
    Hypergeometric2F1[1/4,3/4,7/4,(a-b)*(1-Sin[e+f*x])/(2*(a+b*Sin[e+f*x]))] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[g_.*sin[e_.+f_.*x_]]/(a_+b_.*cos[e_.+f_.*x_])^(3/2),x_Symbol] :=
  4*g*(1-Cos[e+f*x])/(3*f*(a+b)*Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Cos[e+f*x]])*((a+b)*(1+Cos[e+f*x])/(2*(a+b*Cos[e+f*x])))^(1/4)*
    Hypergeometric2F1[1/4,3/4,7/4,(a-b)*(1-Cos[e+f*x])/(2*(a+b*Cos[e+f*x]))] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -g*(1+Sin[e+f*x])*(a+b*Sin[e+f*x])^(m+1)*(-(a-b)*(1-Sin[e+f*x])/((a+b)*(1+Sin[e+f*x])))^(m/2+1)/(f*(a-b)*(m+1)*(g*Cos[e+f*x])^(m+2))*
    Hypergeometric2F1[m+1,m/2+1,m+2,2*(a+b*Sin[e+f*x])/((a+b)*(1+Sin[e+f*x]))] /;
FreeQ[{a,b,e,f,g,p,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[m+p+1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(1+Cos[e+f*x])*(a+b*Cos[e+f*x])^(m+1)*(-(a-b)*(1-Cos[e+f*x])/((a+b)*(1+Cos[e+f*x])))^(m/2+1)/(f*(a-b)*(m+1)*(g*Sin[e+f*x])^(m+2))*
    Hypergeometric2F1[m+1,m/2+1,m+2,2*(a+b*Cos[e+f*x])/((a+b)*(1+Cos[e+f*x]))] /;
FreeQ[{a,b,e,f,g,p,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/
    (b*f*(m+p)*(-b*(1-Sin[e+f*x])/(a+b*Sin[e+f*x]))^((p-1)/2)*(b*(1+Sin[e+f*x])/(a+b*Sin[e+f*x]))^((p-1)/2))*
  AppellF1[-p-m,(1-p)/2,(1-p)/2,1-p-m,(a+b)/(a+b*Sin[e+f*x]),(a-b)/(a+b*Sin[e+f*x])] /;
FreeQ[{a,b,e,f,g,p},x] && NonzeroQ[a^2-b^2] && NegativeIntegerQ[m] && Not[PositiveIntegerQ[m+p+1]]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -g*(g*Sin[e+f*x])^(p-1)*(a+b*Cos[e+f*x])^(m+1)/
    (b*f*(m+p)*(-b*(1-Cos[e+f*x])/(a+b*Cos[e+f*x]))^((p-1)/2)*(b*(1+Cos[e+f*x])/(a+b*Cos[e+f*x]))^((p-1)/2))*
  AppellF1[-p-m,(1-p)/2,(1-p)/2,1-p-m,(a+b)/(a+b*Cos[e+f*x]),(a-b)/(a+b*Cos[e+f*x])] /;
FreeQ[{a,b,e,f,g,p},x] && NonzeroQ[a^2-b^2] && NegativeIntegerQ[m] && Not[PositiveIntegerQ[m+p+1]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/
    (b*f*(m+1)*(1-(a+b*Sin[e+f*x])/(a-b))^((p-1)/2)*(1-(a+b*Sin[e+f*x])/(a+b))^((p-1)/2))*
    AppellF1[m+1,-(p-1)/2,-(p-1)/2,m+2,(a+b*Sin[e+f*x])/(a+b),(a+b*Sin[e+f*x])/(a-b)] /;
FreeQ[{a,b,e,f,g,p,m},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[m]] && Not[NegativeIntegerQ[m+p]]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -g*(g*Sin[e+f*x])^(p-1)*(a+b*Cos[e+f*x])^(m+1)/
    (b*f*(m+1)*(1-(a+b*Cos[e+f*x])/(a-b))^((p-1)/2)*(1-(a+b*Cos[e+f*x])/(a+b))^((p-1)/2))*
    AppellF1[m+1,-(p-1)/2,-(p-1)/2,m+2,(a+b*Cos[e+f*x])/(a+b),(a+b*Cos[e+f*x])/(a-b)] /;
FreeQ[{a,b,e,f,g,p,m},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[m]] && Not[NegativeIntegerQ[m+p]]


(* ::Subsection::Closed:: *)
(*4.2 (g cos)^p (a+b sin)^m (A+B sin)*)


Int[(g_.*cos[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^n,x] + b/d*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && (Not[IntegerQ[(p-1)/2]] || NonzeroQ[a^2-b^2] && RationalQ[p] && p<0 || RationalQ[n,p] && (0<n<p-1 || -2*p<=n<-p-1))


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*cos[e_.+f_.*x_])*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  a*Int[(g*Sin[e+f*x])^p*(d*Cos[e+f*x])^n,x] + b/d*Int[(g*Sin[e+f*x])^p*(d*Cos[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && (Not[OddQ[p]] || NonzeroQ[a^2-b^2] && RationalQ[p] && p<0 || RationalQ[n,p] && (0<n<p-1 || -2*p<=n<-p-1))


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g^2/a*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n,x] - 
  g^2/(b*d)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && ZeroQ[a^2-b^2] && (Not[PositiveIntegerQ[(p+1)/2]] || ZeroQ[n-1] || ZeroQ[p-3] || ZeroQ[n+p] || ZeroQ[n+p+1])


Int[(g_.*sin[e_.+f_.*x_])^p_*(d_.*cos[e_.+f_.*x_])^n_./(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  g^2/a*Int[(g*Sin[e+f*x])^(p-2)*(d*Cos[e+f*x])^n,x] - 
  g^2/(b*d)*Int[(g*Sin[e+f*x])^(p-2)*(d*Cos[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && ZeroQ[a^2-b^2] && (Not[PositiveIntegerQ[(p+1)/2]] || ZeroQ[n-1] || ZeroQ[p-3] || ZeroQ[n+p] || ZeroQ[n+p+1])


Int[cos[e_.+f_.*x_]^p_.*sin[e_.+f_.*x_]^n_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  1/(b^(n+p)*f)*Subst[Int[x^n*(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m,n},x] && IntegerQ[(p-1)/2] && ZeroQ[a^2-b^2] && (IntegerQ[n] || PositiveQ[b])


Int[sin[e_.+f_.*x_]^p_.*cos[e_.+f_.*x_]^n_.*(a_+b_.*cos[e_.+f_.*x_])^m_.,x_Symbol] :=
  -1/(b^(n+p)*f)*Subst[Int[x^n*(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2),x],x,b*Cos[e+f*x]] /;
FreeQ[{a,b,e,f,m,n},x] && IntegerQ[(p-1)/2] && ZeroQ[a^2-b^2] && (IntegerQ[n] || PositiveQ[b])


Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/(b^p*f)*Subst[Int[(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2)*(c+d/b*x)^n,x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,c,d,m,n},x] && IntegerQ[(p-1)/2] && ZeroQ[a^2-b^2]


Int[sin[e_.+f_.*x_]^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -1/(b^p*f)*Subst[Int[(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2)*(c+d/b*x)^n,x],x,b*Cos[e+f*x]] /;
FreeQ[{a,b,e,f,c,d,m,n},x] && IntegerQ[(p-1)/2] && ZeroQ[a^2-b^2]


Int[cos[e_.+f_.*x_]^p_.*sin[e_.+f_.*x_]^n_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  1/(b^(n+p)*f)*Subst[Int[x^n*(a+x)^m*(b^2-x^2)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m,n},x] && IntegerQ[(p-1)/2] && NonzeroQ[a^2-b^2] && (IntegerQ[n] || PositiveQ[b])


Int[sin[e_.+f_.*x_]^p_.*cos[e_.+f_.*x_]^n_.*(a_+b_.*cos[e_.+f_.*x_])^m_.,x_Symbol] :=
  -1/(b^(n+p)*f)*Subst[Int[x^n*(a+x)^m*(b^2-x^2)^((p-1)/2),x],x,b*Cos[e+f*x]] /;
FreeQ[{a,b,e,f,m,n},x] && IntegerQ[(p-1)/2] && NonzeroQ[a^2-b^2] && (IntegerQ[n] || PositiveQ[b])


Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/(b^p*f)*Subst[Int[(a+x)^m*(c+d/b*x)^n*(b^2-x^2)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,c,d,m,n},x] && IntegerQ[(p-1)/2] && NonzeroQ[a^2-b^2]


Int[sin[e_.+f_.*x_]^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -1/(b^p*f)*Subst[Int[(a+x)^m*(c+d/b*x)^n*(b^2-x^2)^((p-1)/2),x],x,b*Cos[e+f*x]] /;
FreeQ[{a,b,e,f,c,d,m,n},x] && IntegerQ[(p-1)/2] && NonzeroQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) /;
FreeQ[{a,b,e,f,g,A,B,m,p},x] && ZeroQ[a^2-b^2] && ZeroQ[a*B*m+A*b*(m+p+1)] && NonzeroQ[m+p+1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(f*g*(m+p+1)) /;
FreeQ[{a,b,e,f,g,A,B,m,p},x] && ZeroQ[a^2-b^2] && ZeroQ[a*B*m+A*b*(m+p+1)] && NonzeroQ[m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) + 
  (a*B*m+A*b*(m+p+1))/(b*(m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,g,A,B,m,p},x] && ZeroQ[a^2-b^2] && PositiveIntegerQ[Simplify[(2*m+p+1)/2]] && NonzeroQ[m+p+1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(f*g*(m+p+1)) + 
  (a*B*m+A*b*(m+p+1))/(b*(m+p+1))*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,g,A,B,m,p},x] && ZeroQ[a^2-b^2] && PositiveIntegerQ[Simplify[(2*m+p+1)/2]] && NonzeroQ[m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(A*b+a*B)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(p+1)) + 
  b*(a*B*m+A*b*(m+p+1))/(a*g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,A,B},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && p<-1 && m>0


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (A*b+a*B)*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(a*f*g*(p+1)) + 
  b*(a*B*m+A*b*(m+p+1))/(a*g^2*(p+1))*Int[(g*Sin[e+f*x])^(p+2)*(a+b*Cos[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,A,B},x] && ZeroQ[a^2-b^2] && RationalQ[m,p] && p<-1 && m>0


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(2*m+p+1)) + 
  (a*B*m+A*b*(m+p+1))/(a*b*(2*m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g,A,B,m,p},x] && ZeroQ[a^2-b^2] && (RationalQ[m] && m<-1 || NegativeIntegerQ[Simplify[m+p]]) && NonzeroQ[2*m+p+1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(a*f*g*(2*m+p+1)) + 
  (a*B*m+A*b*(m+p+1))/(a*b*(2*m+p+1))*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g,A,B,m,p},x] && ZeroQ[a^2-b^2] && (RationalQ[m] && m<-1 || NegativeIntegerQ[Simplify[m+p]]) && NonzeroQ[2*m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) + 
  (a*B*m+A*b*(m+p+1))/(b*(m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,g,A,B,m,p},x] && ZeroQ[a^2-b^2] && NonzeroQ[m+p+1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(f*g*(m+p+1)) + 
  (a*B*m+A*b*(m+p+1))/(b*(m+p+1))*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,g,A,B,m,p},x] && ZeroQ[a^2-b^2] && NonzeroQ[m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(B+A*Sin[e+f*x])/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1)*Simp[a*A*(p+2)+b*B*m+A*b*(m+p+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && m>0 && p<-1


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m*(B+A*Cos[e+f*x])/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Sin[e+f*x])^(p+2)*(a+b*Cos[e+f*x])^(m-1)*Simp[a*A*(p+2)+b*B*m+A*b*(m+p+2)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && m>0 && p<-1


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) + 
  1/(m+p+1)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*Simp[a*A*(m+p+1)+b*B*m+(a*B*m+A*b*(m+p+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B,p},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[p] && p<-1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^m/(f*g*(m+p+1)) + 
  1/(m+p+1)*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m-1)*Simp[a*A*(m+p+1)+b*B*m+(a*B*m+A*b*(m+p+1))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B,p},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[p] && p<-1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)*(A*b*(m+p+1)-a*B*p+b*B*(m+1)*Sin[e+f*x])/(b^2*f*(m+1)*(m+p+1)) + 
  g^2*(p-1)/(b^2*(m+1)*(m+p+1))*
    Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1)*Simp[b*B*(m+1)+(A*b*(m+p+1)-a*B*p)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && NonzeroQ[m+p+1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -g*(g*Sin[e+f*x])^(p-1)*(a+b*Cos[e+f*x])^(m+1)*(A*b*(m+p+1)-a*B*p+b*B*(m+1)*Cos[e+f*x])/(b^2*f*(m+1)*(m+p+1)) + 
  g^2*(p-1)/(b^2*(m+1)*(m+p+1))*
    Int[(g*Sin[e+f*x])^(p-2)*(a+b*Cos[e+f*x])^(m+1)*Simp[b*B*(m+1)+(A*b*(m+p+1)-a*B*p)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B},x] && NonzeroQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && NonzeroQ[m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a^2-b^2)*(m+1)) + 
  1/((a^2-b^2)*(m+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*Simp[(a*A-b*B)*(m+1)-(A*b-a*B)*(m+p+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B,p},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m+1)/(f*g*(a^2-b^2)*(m+1)) + 
  1/((a^2-b^2)*(m+1))*Int[(g*Sin[e+f*x])^p*(a+b*Cos[e+f*x])^(m+1)*Simp[(a*A-b*B)*(m+1)-(A*b-a*B)*(m+p+2)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B,p},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)*(A*b*(m+p+1)-a*B*p+b*B*(m+p)*Sin[e+f*x])/(b^2*f*(m+p)*(m+p+1)) + 
  g^2*(p-1)/(b^2*(m+p)*(m+p+1))*
    Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^m*Simp[b*(a*B*m+A*b*(m+p+1))+(a*A*b*(m+p+1)-B*(a^2*p-b^2*(m+p)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B,m},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p>1 && NonzeroQ[m+p] && NonzeroQ[m+p+1]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -g*(g*Sin[e+f*x])^(p-1)*(a+b*Cos[e+f*x])^(m+1)*(A*b*(m+p+1)-a*B*p+b*B*(m+p)*Cos[e+f*x])/(b^2*f*(m+p)*(m+p+1)) + 
  g^2*(p-1)/(b^2*(m+p)*(m+p+1))*
    Int[(g*Sin[e+f*x])^(p-2)*(a+b*Cos[e+f*x])^m*Simp[b*(a*B*m+A*b*(m+p+1))+(a*A*b*(m+p+1)-B*(a^2*p-b^2*(m+p)))*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B,m},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p>1 && NonzeroQ[m+p] && NonzeroQ[m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)*(A*b-a*B-(a*A-b*B)*Sin[e+f*x])/(f*g*(a^2-b^2)*(p+1)) + 
  1/(g^2*(a^2-b^2)*(p+1))*
    Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m*Simp[A*(a^2*(p+2)-b^2*(m+p+2))+a*b*B*m+b*(a*A-b*B)*(m+p+3)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B,m},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -(g*Sin[e+f*x])^(p+1)*(a+b*Cos[e+f*x])^(m+1)*(A*b-a*B-(a*A-b*B)*Cos[e+f*x])/(f*g*(a^2-b^2)*(p+1)) + 
  1/(g^2*(a^2-b^2)*(p+1))*
    Int[(g*Sin[e+f*x])^(p+2)*(a+b*Cos[e+f*x])^m*Simp[A*(a^2*(p+2)-b^2*(m+p+2))+a*b*B*m+b*(a*A-b*B)*(m+p+3)*Cos[e+f*x],x],x] /;
FreeQ[{a,b,e,f,g,A,B,m},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1


Int[(g_.*cos[e_.+f_.*x_])^p_*(A_.+B_.*sin[e_.+f_.*x_])/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  B/b*Int[(g*Cos[e+f*x])^p,x] + (A*b-a*B)/b*Int[(g*Cos[e+f*x])^p/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,A,B},x] && NonzeroQ[a^2-b^2]


Int[(g_.*sin[e_.+f_.*x_])^p_*(A_.+B_.*cos[e_.+f_.*x_])/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  B/b*Int[(g*Sin[e+f*x])^p,x] + (A*b-a*B)/b*Int[(g*Sin[e+f*x])^p/(a+b*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,A,B},x] && NonzeroQ[a^2-b^2]


Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/a^2*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*(a-b*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && Not[ZeroQ[c] && PositiveIntegerQ[m]]


Int[sin[e_.+f_.*x_]^2*(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/a^2*Int[(a+b*Cos[e+f*x])^(m+1)*(c+d*Cos[e+f*x])^n*(a-b*Cos[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && Not[ZeroQ[c] && PositiveIntegerQ[m]]


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^(2*m)*Int[Cos[e+f*x]^(2*m+p)*(c+d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[a^2-b^2] && IntegersQ[p/2,m] && (m<0 && p<0 || ZeroQ[2*m+p] || ZeroQ[2*m+p-2])


Int[sin[e_.+f_.*x_]^p_*(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^(2*m)*Int[Sin[e+f*x]^(2*m+p)*(c+d*Cos[e+f*x])^n/(a-b*Cos[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[a^2-b^2] && IntegersQ[p/2,m] && (m<0 && p<0 || ZeroQ[2*m+p] || ZeroQ[2*m+p-2])


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/a^p*Int[ExpandTrig[(a-b*sin[e+f*x])^(p/2)*(a+b*sin[e+f*x])^(m+p/2)*(c+d*sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[a^2-b^2] && IntegersQ[p/2,m] && 
  (m<-2 && p>0 || m>2 && p<0 && m+p/2>0 || p>2 && m>=2 && RationalQ[n] && -m-p<n<-1)


Int[sin[e_.+f_.*x_]^p_*(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/a^p*Int[ExpandTrig[(a-b*cos[e+f*x])^(p/2)*(a+b*cos[e+f*x])^(m+p/2)*(c+d*cos[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[a^2-b^2] && IntegersQ[p/2,m] && 
  (m<-2 && p>0 || m>2 && p<0 && m+p/2>0 || p>2 && m>=2 && RationalQ[n] && -m-p<n<-1)


Int[cos[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  -2/(a*b*d)*Int[(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^(n+1),x] + 
  1/a^2*Int[(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^n*(1+Sin[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[e_.+f_.*x_]^4*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -2/(a*b*d)*Int[(a+b*Cos[e+f*x])^(m+2)*(d*Cos[e+f*x])^(n+1),x] + 
  1/a^2*Int[(a+b*Cos[e+f*x])^(m+2)*(d*Cos[e+f*x])^n*(1+Cos[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/d^4*Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n+4),x] + 
  Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^n*(1-2*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && Not[PositiveIntegerQ[m]]


Int[sin[e_.+f_.*x_]^4*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/d^4*Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n+4),x] + 
  Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^n*(1-2*Cos[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && Not[PositiveIntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(g*cos[e+f*x])^p,(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && ZeroQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(g*sin[e+f*x])^p,(a+b*cos[e+f*x])^m*(c+d*cos[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && ZeroQ[a^2-b^2] && PositiveIntegerQ[m]


Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(1-Sin[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[a^2-b^2]


Int[sin[e_.+f_.*x_]^2*(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n*(1-Cos[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[a^2-b^2]


(* Int[cos[e_.+f_.*x_]^4*sin[e_.+f_.*x_]^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (a^2-b^2)*Cos[e+f*x]*Sin[e+f*x]^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(a*b^2*d*(m+1)) - 
  (a^2*(n+1)-b^2*(m+n+2))*Cos[e+f*x]*Sin[e+f*x]^(n+1)*(a+b*Sin[e+f*x])^(m+2)/(a^2*b^2*d*(n+1)*(m+1)) + 
  1/(a^2*b*(n+1)*(m+1))*Int[Sin[e+f*x]^(n+1)*(a+b*Sin[e+f*x])^(m+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*(m+1)*Sin[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n,m] && m<-1 && n<-1 *)


(* Int[sin[e_.+f_.*x_]^4*cos[e_.+f_.*x_]^n_*(a_+b_.*cos[e_.+f_.*x_])^m_,x_Symbol] :=
  -(a^2-b^2)*Sin[e+f*x]*Cos[e+f*x]^(n+1)*(a+b*Cos[e+f*x])^(m+1)/(a*b^2*d*(m+1)) + 
  (a^2*(n+1)-b^2*(m+n+2))*Sin[e+f*x]*Cos[e+f*x]^(n+1)*(a+b*Cos[e+f*x])^(m+2)/(a^2*b^2*d*(n+1)*(m+1)) + 
  1/(a^2*b*(n+1)*(m+1))*Int[Cos[e+f*x]^(n+1)*(a+b*Cos[e+f*x])^(m+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*(m+1)*Cos[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n,m] && m<-1 && n<-1 *)


Int[cos[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*d*f*(n+1)) - 
  (a^2*(n+1)-b^2*(m+n+2))*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+2)/(a^2*b*d^2*f*(n+1)*(m+1)) + 
  1/(a^2*b*d*(n+1)*(m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*(m+1)*Sin[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n,m] && m<-1 && n<-1


Int[sin[e_.+f_.*x_]^4*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+1)/(a*d*f*(n+1)) + 
  (a^2*(n+1)-b^2*(m+n+2))*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+2)/(a^2*b*d^2*f*(n+1)*(m+1)) + 
  1/(a^2*b*d*(n+1)*(m+1))*Int[(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*(m+1)*Cos[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n,m] && m<-1 && n<-1


Int[cos[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  (a^2-b^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*b^2*d*f*(m+1)) + 
  (a^2*(n-m+1)-b^2*(m+n+2))*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^(n+1)/(a^2*b^2*d*f*(m+1)*(m+2)) - 
  1/(a^2*b^2*(m+1)*(m+2))*Int[(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^n*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+3)+a*b*(m+2)*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[RationalQ[n] && n<-1] && (m<-2 || ZeroQ[m+n+4])


Int[sin[e_.+f_.*x_]^4*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -(a^2-b^2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+1)/(a*b^2*d*f*(m+1)) - 
  (a^2*(n-m+1)-b^2*(m+n+2))*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+2)*(d*Cos[e+f*x])^(n+1)/(a^2*b^2*d*f*(m+1)*(m+2)) - 
  1/(a^2*b^2*(m+1)*(m+2))*Int[(a+b*Cos[e+f*x])^(m+2)*(d*Cos[e+f*x])^n*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+3)+a*b*(m+2)*Cos[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+2)*(m+n+4))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[RationalQ[n] && n<-1] && (m<-2 || ZeroQ[m+n+4])


Int[cos[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  (a^2-b^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*b^2*d*f*(m+1)) - 
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^(n+1)/(b^2*d*f*(m+n+4)) - 
  1/(a*b^2*(m+1)*(m+n+4))*Int[(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^n*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4)+a*b*(m+1)*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+3)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[RationalQ[n] && n<-1] && NonzeroQ[m+n+4]


Int[sin[e_.+f_.*x_]^4*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -(a^2-b^2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+1)/(a*b^2*d*f*(m+1)) + 
  Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+2)*(d*Cos[e+f*x])^(n+1)/(b^2*d*f*(m+n+4)) - 
  1/(a*b^2*(m+1)*(m+n+4))*Int[(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^n*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4)+a*b*(m+1)*Cos[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+3)*(m+n+4))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[RationalQ[n] && n<-1] && NonzeroQ[m+n+4]


Int[cos[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*d*f*(n+1)) - 
  b*(m+n+2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+2)/(a^2*d^2*f*(n+1)*(n+2)) - 
  1/(a^2*d^2*(n+1)*(n+2))*Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n+2)*
    Simp[a^2*n*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*m*Sin[e+f*x]-(a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && RationalQ[n] && n<-1 && (n<-2 || ZeroQ[m+n+4])


Int[sin[e_.+f_.*x_]^4*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+1)/(a*d*f*(n+1)) + 
  b*(m+n+2)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+2)/(a^2*d^2*f*(n+1)*(n+2)) - 
  1/(a^2*d^2*(n+1)*(n+2))*Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n+2)*
    Simp[a^2*n*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*m*Cos[e+f*x]-(a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+4))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && RationalQ[n] && n<-1 && (n<-2 || ZeroQ[m+n+4])


Int[cos[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*d*f*(n+1)) - 
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+2)/(b*d^2*f*(m+n+4)) + 
  1/(a*b*d*(n+1)*(m+n+4))*Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+4)+a*b*(m+3)*Sin[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+3)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && RationalQ[n] && n<-1 && NonzeroQ[m+n+4]


Int[sin[e_.+f_.*x_]^4*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+1)/(a*d*f*(n+1)) + 
  Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+2)/(b*d^2*f*(m+n+4)) + 
  1/(a*b*d*(n+1)*(m+n+4))*Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+4)+a*b*(m+3)*Cos[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+3)*(m+n+4))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && RationalQ[n] && n<-1 && NonzeroQ[m+n+4]


Int[cos[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a*(n+3)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(b^2*d*f*(m+n+3)*(m+n+4)) - 
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+2)/(b*d^2*f*(m+n+4)) - 
  1/(b^2*(m+n+3)*(m+n+4))*Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^n*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+3)*(m+n+4)+a*b*m*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+3)*(m+n+5))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && Not[RationalQ[n] && n<-1] && 
  NonzeroQ[m+n+3] && NonzeroQ[m+n+4]


Int[sin[e_.+f_.*x_]^4*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -a*(n+3)*Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+1)/(b^2*d*f*(m+n+3)*(m+n+4)) + 
  Sin[e+f*x]*(a+b*Cos[e+f*x])^(m+1)*(d*Cos[e+f*x])^(n+2)/(b*d^2*f*(m+n+4)) - 
  1/(b^2*(m+n+3)*(m+n+4))*Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^n*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+3)*(m+n+4)+a*b*m*Cos[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+3)*(m+n+5))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && Not[RationalQ[n] && n<-1] && 
  NonzeroQ[m+n+3] && NonzeroQ[m+n+4]


Int[cos[e_.+f_.*x_]^6*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Cos[e+f*x]*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(a*d*f*(n+1)) - 
  b*(m+n+2)*Cos[e+f*x]*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^(m+1)/(a^2*d^2*f*(n+1)*(n+2)) - 
  a*(n+5)*Cos[e+f*x]*(d*Sin[e+f*x])^(n+3)*(a+b*Sin[e+f*x])^(m+1)/(b^2*d^3*f*(m+n+5)*(m+n+6)) + 
  Cos[e+f*x]*(d*Sin[e+f*x])^(n+4)*(a+b*Sin[e+f*x])^(m+1)/(b*d^4*f*(m+n+6)) + 
  1/(a^2*b^2*d^2*(n+1)*(n+2)*(m+n+5)*(m+n+6))*
    Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n+2)*
      Simp[a^4*(n+1)*(n+2)*(n+3)*(n+5)-a^2*b^2*(n+2)*(2*n+1)*(m+n+5)*(m+n+6)+b^4*(m+n+2)*(m+n+3)*(m+n+5)*(m+n+6) + 
        a*b*m*(a^2*(n+1)*(n+2)-b^2*(m+n+5)*(m+n+6))*Sin[e+f*x] - 
        (a^4*(n+1)*(n+2)*(4+n)*(n+5)+b^4*(m+n+2)*(m+n+4)*(m+n+5)*(m+n+6)-a^2*b^2*(n+1)*(n+2)*(m+n+5)*(2*n+2*m+13))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m,n},x] && NonzeroQ[a^2-b^2] && NonzeroQ[n+1] && NonzeroQ[n+2] && NonzeroQ[m+n+5] && NonzeroQ[m+n+6] && 
  Not[PositiveIntegerQ[m]]


Int[sin[e_.+f_.*x_]^6*(a_+b_.*cos[e_.+f_.*x_])^m_*(d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  -Sin[e+f*x]*(d*Cos[e+f*x])^(n+1)*(a+b*Cos[e+f*x])^(m+1)/(a*d*f*(n+1)) + 
  b*(m+n+2)*Sin[e+f*x]*(d*Cos[e+f*x])^(n+2)*(a+b*Cos[e+f*x])^(m+1)/(a^2*d^2*f*(n+1)*(n+2)) + 
  a*(n+5)*Sin[e+f*x]*(d*Cos[e+f*x])^(n+3)*(a+b*Cos[e+f*x])^(m+1)/(b^2*d^3*f*(m+n+5)*(m+n+6)) - 
  Sin[e+f*x]*(d*Cos[e+f*x])^(n+4)*(a+b*Cos[e+f*x])^(m+1)/(b*d^4*f*(m+n+6)) + 
  1/(a^2*b^2*d^2*(n+1)*(n+2)*(m+n+5)*(m+n+6))*
    Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n+2)*
      Simp[a^4*(n+1)*(n+2)*(n+3)*(n+5)-a^2*b^2*(n+2)*(2*n+1)*(m+n+5)*(m+n+6)+b^4*(m+n+2)*(m+n+3)*(m+n+5)*(m+n+6) + 
        a*b*m*(a^2*(n+1)*(n+2)-b^2*(m+n+5)*(m+n+6))*Cos[e+f*x] - 
        (a^4*(n+1)*(n+2)*(4+n)*(n+5)+b^4*(m+n+2)*(m+n+4)*(m+n+5)*(m+n+6)-a^2*b^2*(n+1)*(n+2)*(m+n+5)*(2*n+2*m+13))*Cos[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m,n},x] && NonzeroQ[a^2-b^2] && NonzeroQ[n+1] && NonzeroQ[n+2] && NonzeroQ[m+n+5] && NonzeroQ[m+n+6] && 
  Not[PositiveIntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(g*cos[e+f*x])^p,(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(g*sin[e+f*x])^p,(a+b*cos[e+f*x])^m*(c+d*cos[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -a*g*(g*Cos[e+f*x])^(p-1)/(b^2*f*(p-1)) - 
  g^2/b*Int[(g*Cos[e+f*x])^(p-2)*Sin[e+f*x]^2,x] - 
  g^2*(a^2-b^2)/b^2*Int[(g*Cos[e+f*x])^(p-2)*Sin[e+f*x]/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p>1


Int[(g_.*sin[e_.+f_.*x_])^p_*cos[e_.+f_.*x_]/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -a*g*(g*Sin[e+f*x])^(p-1)/(b^2*f*(p-1)) - 
  g^2/b*Int[(g*Sin[e+f*x])^(p-2)*Cos[e+f*x]^2,x] - 
  g^2*(a^2-b^2)/b^2*Int[(g*Sin[e+f*x])^(p-2)*Cos[e+f*x]/(a+b*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p>1


Int[cos[e_.+f_.*x_]^p_*sin[e_.+f_.*x_]^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  Int[ExpandTrig[cos[e+f*x]^p*sin[e+f*x]^n/(a+b*sin[e+f*x]),x],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p>1 && n>1 && IntegersQ[n,p/2]


Int[sin[e_.+f_.*x_]^p_*cos[e_.+f_.*x_]^n_/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  Int[ExpandTrig[sin[e+f*x]^p*cos[e+f*x]^n/(a+b*cos[e+f*x]),x],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p>1 && n>1 && IntegersQ[n,p/2]


Int[(g_.*cos[e_.+f_.*x_])^p_/(sin[e_.+f_.*x_]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
  1/a*Int[(g*Cos[e+f*x])^p/Sin[e+f*x],x] - b/a*Int[(g*Cos[e+f*x])^p/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p>1


Int[(g_.*sin[e_.+f_.*x_])^p_/(cos[e_.+f_.*x_]*(a_+b_.*cos[e_.+f_.*x_])),x_Symbol] :=
  1/a*Int[(g*Sin[e+f*x])^p/Cos[e+f*x],x] - b/a*Int[(g*Sin[e+f*x])^p/(a+b*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p>1


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g^2/a*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n,x] - 
  b*g^2/(a^2*d)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1),x] - 
  g^2*(a^2-b^2)/(a^2*d^2)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+2)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p>1 && n<0


Int[(g_.*sin[e_.+f_.*x_])^p_*(d_.*cos[e_.+f_.*x_])^n_/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  g^2/a*Int[(g*Sin[e+f*x])^(p-2)*(d*Cos[e+f*x])^n,x] - 
  b*g^2/(a^2*d)*Int[(g*Sin[e+f*x])^(p-2)*(d*Cos[e+f*x])^(n+1),x] - 
  g^2*(a^2-b^2)/(a^2*d^2)*Int[(g*Sin[e+f*x])^(p-2)*(d*Cos[e+f*x])^(n+2)/(a+b*Cos[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p>1 && n<0


Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -a*(g*Cos[e+f*x])^(p+1)/(f*g*(p+1)*(a^2-b^2)) - 
  b/(a^2-b^2)*Int[(g*Cos[e+f*x])^p*Sin[e+f*x]^2,x] - 
  b^2/(g^2*(a^2-b^2))*Int[(g*Cos[e+f*x])^(p+2)*Sin[e+f*x]/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1


Int[(g_.*sin[e_.+f_.*x_])^p_*cos[e_.+f_.*x_]/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  -a*(g*Sin[e+f*x])^(p+1)/(f*g*(p+1)*(a^2-b^2)) - 
  b/(a^2-b^2)*Int[(g*Sin[e+f*x])^p*Cos[e+f*x]^2,x] - 
  b^2/(g^2*(a^2-b^2))*Int[(g*Sin[e+f*x])^(p+2)*Cos[e+f*x]/(a+b*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a*d^2/(a^2-b^2)*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-2),x] - 
  b*d/(a^2-b^2)*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1),x] - 
  a^2*d^2/(g^2*(a^2-b^2))*Int[(g*Cos[e+f*x])^(p+2)*(d*Sin[e+f*x])^(n-2)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p<-1 && n>1


Int[(g_.*sin[e_.+f_.*x_])^p_*(d_.*cos[e_.+f_.*x_])^n_/(a_+b_.*cos[e_.+f_.*x_]),x_Symbol] :=
  a*d^2/(a^2-b^2)*Int[(g*Sin[e+f*x])^p*(d*Cos[e+f*x])^(n-2),x] - 
  b*d/(a^2-b^2)*Int[(g*Sin[e+f*x])^p*(d*Cos[e+f*x])^(n-1),x] - 
  a^2*d^2/(g^2*(a^2-b^2))*Int[(g*Sin[e+f*x])^(p+2)*(d*Cos[e+f*x])^(n-2)/(a+b*Cos[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p<-1 && n>1


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n*(1-sin[e+f*x]^2)^(p/2),x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[a^2-b^2] && IntegersQ[2*m,p/2] && (IntegerQ[m] && m<-1 || p>0)


Int[sin[e_.+f_.*x_]^p_*(a_+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(a+b*cos[e+f*x])^m*(c+d*cos[e+f*x])^n*(1-cos[e+f*x]^2)^(p/2),x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[a^2-b^2] && IntegersQ[2*m,p/2] && (IntegerQ[m] && m<-1 || p>0)


Int[(g_.*cos[e_.+f_.*x_])^p_.*(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Module[{v=ExpandTrig[(g*cos[e+f*x])^p*(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_.+b_.*cos[e_.+f_.*x_])^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  Module[{v=ExpandTrig[(g*sin[e+f*x])^p*(a+b*cos[e+f*x])^m*(c+d*cos[e+f*x])^n,x]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[(g_.*cos[e_.+f_.*x_])^p_.*(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(g*cos[e+f*x])^p*(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(g*sin[e+f*x])^p*(a+b*cos[e+f*x])^m*(c+d*cos[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


(* ::Subsection::Closed:: *)
(*7 trig^m (a cos+b sin)^n*)


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(b*d*n) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -1/d*Subst[Int[(a^2+b^2-x^2)^((n-1)/2),x],x,b*Cos[c+d*x]-a*Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && PositiveIntegerQ[(n-1)/2]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(b*Cos[c+d*x]-a*Sin[c+d*x])*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*n) +
  (n-1)*(a^2+b^2)/n*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && Not[OddQ[n]] && RationalQ[n] && n>1


Int[1/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -1/d*Subst[Int[1/(a^2+b^2-x^2),x],x,b*Cos[c+d*x]-a*Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[1/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^2,x_Symbol] :=
  Sin[c+d*x]/(a*d*(a*Cos[c+d*x]+b*Sin[c+d*x])) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cos[c+d*x]-a*Sin[c+d*x])*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) +
  (n+2)/((n+1)*(a^2+b^2))*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && n!=-2


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a^2+b^2)^(n/2)*Int[(Cos[c+d*x-ArcTan[a,b]])^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n] && (n>=1 || n<=-1)] && PositiveQ[a^2+b^2]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a*Cos[c+d*x]+b*Sin[c+d*x])^n/((a*Cos[c+d*x]+b*Sin[c+d*x])/Sqrt[a^2+b^2])^n*Int[Cos[c+d*x-ArcTan[a,b]]^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n] && (n>=1 || n<=-1)] && Not[PositiveQ[a^2+b^2] || ZeroQ[a^2+b^2]]


Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)*Sin[c+d*x]^(n-1)) + 
  2*b*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/Sin[c+d*x]^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && ZeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)*Cos[c+d*x]^(n-1)) + 
  2*a*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/Cos[c+d*x]^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && ZeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*b*d*n*Sin[c+d*x]^n) + 
  1/(2*b)*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/Sin[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*a*d*n*Cos[c+d*x]^n) + 
  1/(2*a)*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/Cos[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*b*d*n*Sin[c+d*x]^n)*Hypergeometric2F1[1,n,n+1,(b+a*Cot[c+d*x])/(2*b)] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[m+n] && ZeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*a*d*n*Cos[c+d*x]^n)*Hypergeometric2F1[1,n,n+1,(a+b*Tan[c+d*x])/(2*a)] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[m+n] && ZeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(b+a*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && IntegerQ[n] && NonzeroQ[a^2+b^2]


Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && IntegerQ[n] && NonzeroQ[a^2+b^2]


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/d*Subst[Int[x^m*(a+b*x)^n/(1+x^2)^((m+n+2)/2),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && IntegerQ[(m+n)/2] && n!=-1 && Not[n>0 && m>1]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -1/d*Subst[Int[x^m*(b+a*x)^n/(1+x^2)^((m+n+2)/2),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && IntegerQ[(m+n)/2] && n!=-1 && Not[n>0 && m>1]


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[sin[c+d*x]^m*(a*cos[c+d*x]+b*sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && PositiveIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*(a*cos[c+d*x]+b*sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && PositiveIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a^n*b^n*Int[Sin[c+d*x]^m*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-n),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2] && NegativeIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a^n*b^n*Int[Cos[c+d*x]^m*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-n),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2] && NegativeIntegerQ[n]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/sin[c_.+d_.*x_],x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)) + 
  b*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] + 
  a^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2)/Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/cos[c_.+d_.*x_],x_Symbol] :=
  -b*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)) + 
  a*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] + 
  b^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2)/Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a^2+b^2)*Int[Sin[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] + 
  2*b*Int[Sin[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] + 
  a^2*Int[Sin[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m<-1


Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a^2+b^2)*Int[Cos[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] + 
  2*a*Int[Cos[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] + 
  b^2*Int[Cos[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m<-1


Int[sin[c_.+d_.*x_]/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  b*x/(a^2+b^2) - 
  a/(a^2+b^2)*Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[cos[c_.+d_.*x_]/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  a*x/(a^2+b^2) + 
  b/(a^2+b^2)*Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[sin[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -a*Sin[c+d*x]^(m-1)/(d*(a^2+b^2)*(m-1)) + 
  b/(a^2+b^2)*Int[Sin[c+d*x]^(m-1),x] + 
  a^2/(a^2+b^2)*Int[Sin[c+d*x]^(m-2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>1


Int[cos[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  b*Cos[c+d*x]^(m-1)/(d*(a^2+b^2)*(m-1)) + 
  a/(a^2+b^2)*Int[Cos[c+d*x]^(m-1),x] + 
  b^2/(a^2+b^2)*Int[Cos[c+d*x]^(m-2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>1


Int[1/(sin[c_.+d_.*x_]*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[Cot[c+d*x],x] - 
  1/a*Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[1/(cos[c_.+d_.*x_]*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  1/b*Int[Tan[c+d*x],x] + 
  1/b*Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[sin[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Sin[c+d*x]^(m+1)/(a*d*(m+1)) - 
  b/a^2*Int[Sin[c+d*x]^(m+1),x] + 
  (a^2+b^2)/a^2*Int[Sin[c+d*x]^(m+2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]^(m+1)/(b*d*(m+1)) - 
  a/b^2*Int[Cos[c+d*x]^(m+1),x] + 
  (a^2+b^2)/b^2*Int[Cos[c+d*x]^(m+2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/sin[c_.+d_.*x_],x_Symbol] :=
  -(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(a*d*(n+1)) - 
  b/a^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] + 
  1/a^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2)/Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/cos[c_.+d_.*x_],x_Symbol] :=
  (a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) - 
  a/b^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] + 
  1/b^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2)/Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a^2+b^2)/a^2*Int[Sin[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] - 
  2*b/a^2*Int[Sin[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] + 
  1/a^2*Int[Sin[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m<-1


Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a^2+b^2)/b^2*Int[Cos[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] - 
  2*a/b^2*Int[Cos[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] + 
  1/b^2*Int[Cos[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m<-1


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_.,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n*(a*cos[c+d*x]+b*sin[c+d*x])^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && PositiveIntegerQ[p]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  a^p*b^p*Int[Cos[c+d*x]^m*Sin[c+d*x]^n*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-p),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2+b^2] && NegativeIntegerQ[p]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_./(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  b/(a^2+b^2)*Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1),x] +
  a/(a^2+b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n,x] -
  a*b/(a^2+b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^(n-1)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && IntegersQ[m,n] && m>0 && n>0


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_./(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n/(a*cos[c+d*x]+b*sin[c+d*x]),x],x] /;
FreeQ[{a,b,c,d,m,n},x] && IntegersQ[m,n]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  b/(a^2+b^2)*Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(p+1),x] +
  a/(a^2+b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n*(a*Cos[c+d*x]+b*Sin[c+d*x])^(p+1),x] -
  a*b/(a^2+b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^(n-1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && IntegersQ[m,n,p] && m>0 && n>0 && p<0


(* ::Subsection::Closed:: *)
(*8 (a+b cos+c sin)^n*)


Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  -2*(c*Cos[d+e*x]-b*Sin[d+e*x])/(e*Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2]


Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)/(e*n) +
  a*(2*n-1)/n*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2] && RationalQ[n] && n>0


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  -(c-a*Sin[d+e*x])/(c*e*(c*Cos[d+e*x]-b*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2]


Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Int[1/Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2]


Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2] && RationalQ[n] && n<-1


Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  b/(c*e)*Subst[Int[Sqrt[a+x]/x,x],x,b*Cos[d+e*x]+c*Sin[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2+c^2]


Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Int[Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2+c^2] && PositiveQ[a+Sqrt[b^2+c^2]]


Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/Sqrt[(a+b*Cos[d+e*x]+c*Sin[d+e*x])/(a+Sqrt[b^2+c^2])]*
    Int[Sqrt[a/(a+Sqrt[b^2+c^2])+Sqrt[b^2+c^2]/(a+Sqrt[b^2+c^2])*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2] && NonzeroQ[b^2+c^2] && Not[PositiveQ[a+Sqrt[b^2+c^2]]]


Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)/(e*n) +
  1/n*Int[Simp[n*a^2+(n-1)*(b^2+c^2)+a*b*(2*n-1)*Cos[d+e*x]+a*c*(2*n-1)*Sin[d+e*x],x]*
    (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n>1


(* Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  x/Sqrt[a^2-b^2-c^2] + 
  2/(e*Sqrt[a^2-b^2-c^2])*ArcTan[(c*Cos[d+e*x]-b*Sin[d+e*x])/(a+Sqrt[a^2-b^2-c^2]+b*Cos[d+e*x]+c*Sin[d+e*x])] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[a^2-b^2-c^2] *)


(* Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Log[RemoveContent[b^2+c^2+(a*b-c*Rt[-a^2+b^2+c^2,2])*Cos[d+e*x]+(a*c+b*Sqrt[-a^2+b^2+c^2])*Sin[d+e*x],x]]/
    (2*e*Rt[-a^2+b^2+c^2,2]) - 
  Log[RemoveContent[b^2+c^2+(a*b+c*Rt[-a^2+b^2+c^2,2])*Cos[d+e*x]+(a*c-b*Sqrt[-a^2+b^2+c^2])*Sin[d+e*x],x]]/
    (2*e*Rt[-a^2+b^2+c^2,2]) /;
FreeQ[{a,b,c,d,e},x] && NegativeQ[a^2-b^2-c^2] *)


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Module[{f=FreeFactors[Cot[(d+e*x)/2],x]},
  -f/e*Subst[Int[1/(a+c*f*x),x],x,Cot[(d+e*x)/2]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a+b]


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Module[{f=FreeFactors[Tan[(d+e*x)/2+Pi/4],x]},
  f/e*Subst[Int[1/(a+b*f*x),x],x,Tan[(d+e*x)/2+Pi/4]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a+c]


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Module[{f=FreeFactors[Cot[(d+e*x)/2+Pi/4],x]},
  -f/e*Subst[Int[1/(a+b*f*x),x],x,Cot[(d+e*x)/2+Pi/4]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a-c] && NonzeroQ[a-b]


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Module[{f=FreeFactors[Tan[(d+e*x)/2],x]},
  2*f/e*Subst[Int[1/(a+b+2*c*f*x+(a-b)*f^2*x^2),x],x,Tan[(d+e*x)/2]/f]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2]


Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  b/(c*e)*Subst[Int[1/(x*Sqrt[a+x]),x],x,b*Cos[d+e*x]+c*Sin[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2+c^2]


Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Int[1/Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2+c^2] && PositiveQ[a+Sqrt[b^2+c^2]]


Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Sqrt[(a+b*Cos[d+e*x]+c*Sin[d+e*x])/(a+Sqrt[b^2+c^2])]/Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]*
    Int[1/Sqrt[a/(a+Sqrt[b^2+c^2])+Sqrt[b^2+c^2]/(a+Sqrt[b^2+c^2])*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2] && NonzeroQ[b^2+c^2] && Not[PositiveQ[a+Sqrt[b^2+c^2]]]


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^(3/2),x_Symbol] :=
  2*(c*Cos[d+e*x]-b*Sin[d+e*x])/(e*(a^2-b^2-c^2)*Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]) +
  1/(a^2-b^2-c^2)*Int[Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2]


Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (-c*Cos[d+e*x]+b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/(e*(n+1)*(a^2-b^2-c^2)) +
  1/((n+1)*(a^2-b^2-c^2))*
    Int[(a*(n+1)-b*(n+2)*Cos[d+e*x]-c*(n+2)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n<-1 && n!=-3/2


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-b*B-c*C)*x/(2*a^2) - (b*B+c*C)*(b*Cos[d+e*x]-c*Sin[d+e*x])/(2*a*b*c*e) + 
  (a^2*(b*B-c*C)-2*a*A*b^2+b^2*(b*B+c*C))*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*b*c*e) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && ZeroQ[b^2+c^2]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-c*C)*x/(2*a^2) - C*Cos[d+e*x]/(2*a*e) + c*C*Sin[d+e*x]/(2*a*b*e) + 
  (-a^2*C+2*a*c*A+b^2*C)*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*b*e) /;
FreeQ[{a,b,c,d,e,A,C},x] && ZeroQ[b^2+c^2]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-b*B)*x/(2*a^2) - b*B*Cos[d+e*x]/(2*a*c*e) + B*Sin[d+e*x]/(2*a*e) + 
  (a^2*B-2*a*b*A+b^2*B)*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*c*e) /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2+c^2]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (b*B+c*C)*x/(b^2+c^2) + (c*B-b*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[b^2+c^2] && ZeroQ[A*(b^2+c^2)-a*(b*B+c*C)]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  c*C*x/(b^2+c^2) - b*C*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[b^2+c^2] && ZeroQ[A*(b^2+c^2)-a*c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  b*B*x/(b^2+c^2) + c*B*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2+c^2] && ZeroQ[A*(b^2+c^2)-a*b*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (b*B+c*C)*x/(b^2+c^2) + (c*B-b*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  (A*(b^2+c^2)-a*(b*B+c*C))/(b^2+c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[b^2+c^2] && NonzeroQ[A*(b^2+c^2)-a*(b*B+c*C)]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  c*C*(d+e*x)/(e*(b^2+c^2)) - b*C*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  (A*(b^2+c^2)-a*c*C)/(b^2+c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[b^2+c^2] && NonzeroQ[A*(b^2+c^2)-a*c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  b*B*(d+e*x)/(e*(b^2+c^2)) +
  c*B*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  (A*(b^2+c^2)-a*b*B)/(b^2+c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2+c^2] && NonzeroQ[A*(b^2+c^2)-a*b*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
FreeQ[{a,b,c,d,e,A,B,C,n},x] && NonzeroQ[n+1] && ZeroQ[a^2-b^2-c^2] && ZeroQ[(b*B+c*C)*n+a*A*(n+1)]


Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
FreeQ[{a,b,c,d,e,A,C,n},x] && NonzeroQ[n+1] && ZeroQ[a^2-b^2-c^2] && ZeroQ[c*C*n+a*A*(n+1)]


Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
FreeQ[{a,b,c,d,e,A,B,n},x] && NonzeroQ[n+1] && ZeroQ[a^2-b^2-c^2] && ZeroQ[b*B*n+a*A*(n+1)]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  ((b*B+c*C)*n+a*A*(n+1))/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,C,n},x] && NonzeroQ[n+1] && ZeroQ[a^2-b^2-c^2] && NonzeroQ[(b*B+c*C)*n+a*A*(n+1)]


Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  (c*C*n+a*A*(n+1))/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,C,n},x] && NonzeroQ[n+1] && ZeroQ[a^2-b^2-c^2] && NonzeroQ[c*C*n+a*A*(n+1)]


Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  (b*B*n+a*A*(n+1))/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,n},x] && NonzeroQ[n+1] && ZeroQ[a^2-b^2-c^2] && NonzeroQ[b*B*n+a*A*(n+1)]


Int[(B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (c*B-b*C)*(b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/(e*(n+1)*(b^2+c^2)) /;
FreeQ[{b,c,d,e,B,C},x] && NonzeroQ[n+1] && NonzeroQ[b^2+c^2] && ZeroQ[b*B+c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  1/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
	Simp[a*(b*B+c*C)*n+a^2*A*(n+1)+
      (n*(a^2*B-B*c^2+b*c*C)+a*b*A*(n+1))*Cos[d+e*x]+
      (n*(b*B*c+a^2*C-b^2*C)+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && RationalQ[n] && n>0 && NonzeroQ[a^2-b^2-c^2]


Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  1/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
    Simp[a*c*C*n+a^2*A*(n+1)+(c*b*C*n+a*b*A*(n+1))*Cos[d+e*x]+(a^2*C*n-b^2*C*n+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,C},x] && RationalQ[n] && n>0 && NonzeroQ[a^2-b^2-c^2]


Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  1/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
    Simp[a*b*B*n+a^2*A*(n+1)+(a^2*B*n-c^2*B*n+a*b*A*(n+1))*Cos[d+e*x]+(b*c*B*n+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && RationalQ[n] && n>0 && NonzeroQ[a^2-b^2-c^2]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  B/b*Int[Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] +
  (A*b-a*B)/b*Int[1/Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && ZeroQ[B*c-b*C] && NonzeroQ[A*b-a*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/
    (e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2-c^2] && ZeroQ[a*A-b*B-c*C]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  -(b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2-c^2] && ZeroQ[a*A-c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2-c^2] && ZeroQ[a*A-b*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/
    (e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  (a*A-b*B-c*C)/(a^2-b^2-c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2-c^2] && NonzeroQ[a*A-b*B-c*C]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  -(b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  (a*A-c*C)/(a^2-b^2-c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2-c^2] && NonzeroQ[a*A-c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  (a*A-b*B)/(a^2-b^2-c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2-c^2] && NonzeroQ[a*A-b*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  1/((n+1)*(a^2-b^2-c^2))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
    Simp[(n+1)*(a*A-b*B-c*C)+(n+2)*(a*B-b*A)*Cos[d+e*x]+(n+2)*(a*C-c*A)*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2-c^2] && n!=-2


Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  1/((n+1)*(a^2-b^2-c^2))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
    Simp[(n+1)*(a*A-c*C)-(n+2)*b*A*Cos[d+e*x]+(n+2)*(a*C-c*A)*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,C},x] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2-c^2] && n!=-2


Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  1/((n+1)*(a^2-b^2-c^2))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
    Simp[(n+1)*(a*A-b*B)+(n+2)*(a*B-b*A)*Cos[d+e*x]-(n+2)*c*A*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2-c^2] && n!=-2


Int[1/(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]),x_Symbol] :=
  Int[Cos[d+e*x]/(b+a*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e},x]


Int[1/(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]),x_Symbol] :=
  Int[Sin[d+e*x]/(b+a*Sin[d+e*x]+c*Cos[d+e*x]),x] /;
FreeQ[{a,b,c,d,e},x]


Int[cos[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^n_.,x_Symbol] :=
  Int[(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[n]


Int[sin[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^n_.,x_Symbol] :=
  Int[(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[n]


Int[cos[d_.+e_.*x_]^n_*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^n_,x_Symbol] :=
  Cos[d+e*x]^n*(a+b*Sec[d+e*x]+c*Tan[d+e*x])^n/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n*Int[(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[sin[d_.+e_.*x_]^n_*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^n_,x_Symbol] :=
  Sin[d+e*x]^n*(a+b*Csc[d+e*x]+c*Cot[d+e*x])^n/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n*Int[(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[sec[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^m_,x_Symbol] :=
  Int[1/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[m+n] && IntegerQ[n]


Int[csc[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^m_,x_Symbol] :=
  Int[1/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[m+n] && IntegerQ[n]


Int[sec[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^m_,x_Symbol] :=
  Sec[d+e*x]^n*(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n/(a+b*Sec[d+e*x]+c*Tan[d+e*x])^n*Int[1/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[m+n] && Not[IntegerQ[n]]


Int[csc[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^m_,x_Symbol] :=
  Csc[d+e*x]^n*(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n/(a+b*Csc[d+e*x]+c*Cot[d+e*x])^n*Int[1/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[m+n] && Not[IntegerQ[n]]


(* ::Subsection::Closed:: *)
(*9 trig^m (a+b sin^n)^p*)


Int[(a_+b_.*sin[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  a^p*Int[Cos[c+d*x]^(2*p),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b] && IntegerQ[p]


Int[(a_+b_.*cos[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  a^p*Int[Sin[c+d*x]^(2*p),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b] && IntegerQ[p]


Int[(a_+b_.*sin[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Int[(a*Cos[c+d*x]^2)^p,x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[a+b] && Not[IntegerQ[p]]


Int[(a_+b_.*cos[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Int[(a*Sin[c+d*x]^2)^p,x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[a+b] && Not[IntegerQ[p]]


Int[(a_+b_.*sin[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  e/d*Subst[Int[(a+(a+b)*e^2*x^2)^p/(1+e^2*x^2)^(p+1),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p]


Int[(a_+b_.*cos[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  e/d*Subst[Int[(a+b+a*e^2*x^2)^p/(1+e^2*x^2)^(p+1),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p]


(* Int[(a_+b_.*cos[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Module[{e=FreeFactors[Cot[c+d*x],x]},
  -e/d*Subst[Int[(a+(a+b)*e^2*x^2)^p/(1+e^2*x^2)^(p+1),x],x,Cot[c+d*x]/e]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] *)


Int[(a_+b_.*sin[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  1/2^p*Int[(2*a+b-b*Cos[2*c+2*d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[a+b] && Not[IntegerQ[p]]


Int[(a_+b_.*cos[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  1/2^p*Int[(2*a+b+b*Cos[2*c+2*d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[a+b] && Not[IntegerQ[p]]


Int[(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[Expand[(a+b*Sin[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && PositiveIntegerQ[p]


Int[(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[Expand[(a+b*Cos[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && PositiveIntegerQ[p]


Int[(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f/d*Subst[Int[ExpandToSum[b+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(n*p/2+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[n] && IntegerQ[p] && p<-1


Int[(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f/d*Subst[Int[ExpandToSum[b+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(n*p/2+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[n] && IntegerQ[p] && p<-1


Int[u_*(a_+b_.*sin[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  a^p*Int[ActivateTrig[u]*Cos[c+d*x]^(2*p),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b] && IntegerQ[p]


Int[u_*(a_+b_.*cos[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  a^p*Int[ActivateTrig[u]*Sin[c+d*x]^(2*p),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b] && IntegerQ[p]


Int[u_*(a_+b_.*sin[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  (a*Cos[c+d*x]^2)^p/Cos[c+d*x]^(2*p)*Int[ActivateTrig[u]*Cos[c+d*x]^(2*p),x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[a+b] && Not[IntegerQ[p]]


Int[u_*(a_+b_.*cos[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  (a*Sin[c+d*x]^2)^p/Sin[c+d*x]^(2*p)*Int[ActivateTrig[u]*Sin[c+d*x]^(2*p),x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[a+b] && Not[IntegerQ[p]]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f/d*Subst[Int[ExpandToSum[b+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[n] && EvenQ[m] && IntegerQ[p]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f/d*Subst[Int[ExpandToSum[b+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[n] && EvenQ[m] && IntegerQ[p]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*ExpandToSum[a+b*(1-f^2*x^2)^(n/2),x]^p,x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d,p},x] && EvenQ[n] && OddQ[m]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*ExpandToSum[a+b*(1-f^2*x^2)^(n/2),x]^p,x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d,p},x] && EvenQ[n] && OddQ[m]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[sin[c+d*x]^m*(a+b*sin[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[m,n,p]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*(a+b*cos[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[m,n,p]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f/d*Subst[Int[ExpandToSum[b*f^n*x^n+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(m/2+n*(p/2)+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && EvenQ[n] && IntegerQ[p]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f/d*Subst[Int[ExpandToSum[b*f^n*x^n+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(m/2+n*(p/2)+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && EvenQ[n] && IntegerQ[p]


(* Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f^(m+1)/d*Subst[Int[x^m*ExpandToSum[b+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(m/2+n*(p/2)+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && EvenQ[n] && IntegerQ[p] *)


(* Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f^(m+1)/d*Subst[Int[x^m*ExpandToSum[b+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(m/2+n*(p/2)+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && EvenQ[n] && IntegerQ[p] *)


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[Expand[(1-Sin[c+d*x]^2)^(m/2)*(a+b*Sin[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && OddQ[n] && IntegerQ[p] && m>0


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[Expand[(1-Cos[c+d*x]^2)^(m/2)*(a+b*Cos[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && OddQ[n] && IntegerQ[p] && m>0


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[(1-sin[c+d*x]^2)^(m/2)*(a+b*sin[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && OddQ[n] && IntegerQ[p] && m<0 && p<-1


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[(1-cos[c+d*x]^2)^(m/2)*(a+b*cos[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && OddQ[n] && IntegerQ[p] && m<0 && p<-1


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*(e_.*sin[c_.+d_.*x_])^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(a+b*(e*f*x)^n)^p,x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && OddQ[m]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*(e_.*cos[c_.+d_.*x_])^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(a+b*(e*f*x)^n)^p,x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && OddQ[m]


Int[tan[c_.+d_.*x_]^m_.*(a_+b_.*(e_.*sin[c_.+d_.*x_])^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f^(m+1)/d*Subst[Int[x^m*(a+b*(e*f*x)^n)^p/(1-f^2*x^2)^((m+1)/2),x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n},x] && OddQ[m] && IntegerQ[2*p]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*(e_.*cos[c_.+d_.*x_])^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f^(m+1)/d*Subst[Int[x^m*(a+b*(e*f*x)^n)^p/(1-f^2*x^2)^((m+1)/2),x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n},x] && OddQ[m] && IntegerQ[2*p]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f^(m+1)/d*Subst[Int[x^m*ExpandToSum[b*f^n*x^n+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(n*p/2+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,m},x] && Not[OddQ[m]] && EvenQ[n] && IntegerQ[p]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f^(m+1)/d*Subst[Int[x^m*ExpandToSum[b*f^n*x^n+a*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(n*p/2+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,m},x] && Not[OddQ[m]] && EvenQ[n] && IntegerQ[p]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f^(m+1)/d*Subst[Int[x^m*(ExpandToSum[b*f^n*x^n+a*(1+f^2*x^2)^(n/2),x]/(1+f^2*x^2)^(n/2))^p/(1+f^2*x^2),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,m,p},x] && Not[OddQ[m]] && EvenQ[n] && Not[IntegerQ[p]]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f^(m+1)/d*Subst[Int[x^m*(ExpandToSum[b*f^n*x^n+a*(1+f^2*x^2)^(n/2),x]/(1+f^2*x^2)^(n/2))^p/(1+f^2*x^2),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,m,p},x] && Not[OddQ[m]] && EvenQ[n] && Not[IntegerQ[p]]


(* ::Subsection::Closed:: *)
(*10 trig^m (a+b cos^p+c sin^q)^n*)


Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<p<=q


Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<p<=q


Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
    Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<q<p


Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
    Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<q<p


Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<p<=q


Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<p<=q


Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
    Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<q<p


Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
    Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<q<p


(* ::Subsection::Closed:: *)
(*11 trig^m (a+b sin^n+c sin^(2 n))^p*)


Int[(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[u*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[u*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[1/(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Sin[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Sin[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[1/(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Cos[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Cos[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Sin[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Cos[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[Sin[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[Cos[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  Int[ExpandTrig[sin[d+e*x]^m*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && IntegersQ[m,n,p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  Int[ExpandTrig[cos[d+e*x]^m*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && IntegersQ[m,n,p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*sin[d_.+e_.*x_])^n_.+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p,x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && OddQ[m]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*cos[d_.+e_.*x_])^n_.+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p,x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && OddQ[m]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Cos[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Sin[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[Cos[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[Sin[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[(1-sin[d+e*x]^2)^(m/2)*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && IntegersQ[n,p]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[(1-cos[d+e*x]^2)^(m/2)*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && IntegersQ[n,p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*sin[d_.+e_.*x_])^n_+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g^(m+1)/e*Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1-g^2*x^2)^((m+1)/2),x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n},x] && OddQ[m] && IntegerQ[2*p]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*cos[d_.+e_.*x_])^n_+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g^(m+1)/e*Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1-g^2*x^2)^((m+1)/2),x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n},x] && OddQ[m] && IntegerQ[2*p]


Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Tan[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Cot[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[Tan[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[Cot[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c*x^(2*n)+b*x^n*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && NonzeroQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c*x^(2*n)+b*x^n*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && NonzeroQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[sin[d+e*x]^m*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p/(1-sin[d+e*x]^2)^(m/2),x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && IntegersQ[n,p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[cos[d+e*x]^m*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p/(1-cos[d+e*x]^2)^(m/2),x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && IntegersQ[n,p]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*sin[d_.+e_.*x_])^n_+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g^(m+1)/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/x^m,x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n},x] && OddQ[m] && IntegerQ[2*p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*cos[d_.+e_.*x_])^n_+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g^(m+1)/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/x^m,x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n},x] && OddQ[m] && IntegerQ[2*p]


Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Cot[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Tan[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[Cot[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[Tan[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && Not[OddQ[m]] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c+b*(1+f^2*x^2)^(n/2)+a*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[n2-2*n] && EvenQ[n] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c+b*(1+f^2*x^2)^(n/2)+a*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[n2-2*n] && EvenQ[n] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[(1-sin[d+e*x]^2)^(m/2)*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p/sin[d+e*x]^m,x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && IntegersQ[n,p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[(1-cos[d+e*x]^2)^(m/2)*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p/cos[d+e*x]^m,x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && NonzeroQ[b^2-4*a*c] && IntegersQ[n,p]


Int[(A_+B_.*sin[d_.+e_.*x_])*(a_+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Sin[d+e*x])*(b+2*c*Sin[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Cos[d+e*x])*(b+2*c*Cos[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*sin[d_.+e_.*x_])*(a_+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Sin[d+e*x]+c*Sin[d+e*x]^2)^n/(b+2*c*Sin[d+e*x])^(2*n)*Int[(A+B*Sin[d+e*x])*(b+2*c*Sin[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Cos[d+e*x]+c*Cos[d+e*x]^2)^n/(b+2*c*Cos[d+e*x])^(2*n)*Int[(A+B*Cos[d+e*x])*(b+2*c*Cos[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*sin[d_.+e_.*x_])/(a_.+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Sin[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Cos[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Cos[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*sin[d_.+e_.*x_])*(a_.+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*sin[d+e*x])*(a+b*sin[d+e*x]+c*sin[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*cos[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*cos[d+e*x])*(a+b*cos[d+e*x]+c*cos[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c] && IntegerQ[n]


(* ::Subsection::Closed:: *)
(*12 Sine normalization rules*)


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m*Int[ActivateTrig[u]*(d*Sin[a+b*x])^(m+n)/(d*Cos[a+b*x])^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m*Int[ActivateTrig[u]*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^m*Int[ActivateTrig[u]*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^m*Int[ActivateTrig[u]*(d*Cos[a+b*x])^(m+n)/(d*Sin[a+b*x])^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*sec[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Sec[a+b*x])^m*(d*Cos[a+b*x])^m*Int[ActivateTrig[u]*(d*Cos[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*sec[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Csc[a+b*x])^m*(d*Sin[a+b*x])^m*Int[ActivateTrig[u]*(d*Sin[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(c*Cos[a+b*x])^m/(c*Sin[a+b*x])^m*Int[ActivateTrig[u]*(c*Sin[a+b*x])^m/(c*Cos[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(c*Sin[a+b*x])^m/(c*Cos[a+b*x])^m*Int[ActivateTrig[u]*(c*Cos[a+b*x])^m/(c*Sin[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*sec[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Sec[a+b*x])^m*(c*Cos[a+b*x])^m*Int[ActivateTrig[u]/(c*Cos[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*csc[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Csc[a+b*x])^m*(c*Sin[a+b*x])^m*Int[ActivateTrig[u]/(c*Sin[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*sin[a_.+b_.*x_])^n_.*(A_+B_.*csc[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-1)*(B+A*Sin[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*cos[a_.+b_.*x_])^n_.*(A_+B_.*sec[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-1)*(B+A*Cos[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_+B_.*csc[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Sin[a+b*x])/Sin[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_+B_.*sec[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Cos[a+b*x])/Cos[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownSineIntegrandQ[u,x]


Int[u_.*(c_.*sin[a_.+b_.*x_])^n_.*(A_.+B_.*csc[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-2)*(C+B*Sin[a+b*x]+A*Sin[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownSineIntegrandQ[u,x]


Int[u_.*(c_.*cos[a_.+b_.*x_])^n_.*(A_.+B_.*sec[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-2)*(C+B*Cos[a+b*x]+A*Cos[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownSineIntegrandQ[u,x]


Int[u_.*(c_.*sin[a_.+b_.*x_])^n_.*(A_+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-2)*(C+A*Sin[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownSineIntegrandQ[u,x]


Int[u_.*(c_.*cos[a_.+b_.*x_])^n_.*(A_+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-2)*(C+A*Cos[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_.+B_.*csc[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Sin[a+b*x]+A*Sin[a+b*x]^2)/Sin[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_.+B_.*sec[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Cos[a+b*x]+A*Cos[a+b*x]^2)/Cos[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Sin[a+b*x]^2)/Sin[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Cos[a+b*x]^2)/Cos[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_.+B_.*sin[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Sin[a+b*x]+B*Sin[a+b*x]^2)/Sin[a+b*x],x] /;
FreeQ[{a,b,A,B,C},x]


Int[u_*(A_.+B_.*cos[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Cos[a+b*x]+B*Cos[a+b*x]^2)/Cos[a+b*x],x] /;
FreeQ[{a,b,A,B,C},x]


Int[u_*(A_.*sin[a_.+b_.*x_]^n_.+B_.*sin[a_.+b_.*x_]^n1_+C_.*sin[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Sin[a+b*x]^n*(A+B*Sin[a+b*x]+C*Sin[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && ZeroQ[n1-n-1] && ZeroQ[n2-n-2]


Int[u_*(A_.*cos[a_.+b_.*x_]^n_.+B_.*cos[a_.+b_.*x_]^n1_+C_.*cos[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Cos[a+b*x]^n*(A+B*Cos[a+b*x]+C*Cos[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && ZeroQ[n1-n-1] && ZeroQ[n2-n-2]
