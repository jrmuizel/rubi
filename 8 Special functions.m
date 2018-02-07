(* ::Package:: *)

(* ::Section:: *)
(*8 Special functions integration rules*)


(* ::Subsection::Closed:: *)
(*8.1 Error functions*)


Int[Erf[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*Erf[a+b*x]/b + 1/(b*Sqrt[Pi]*E^(a+b*x)^2) /;
FreeQ[{a,b},x]


Int[Erfc[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*Erfc[a+b*x]/b - 1/(b*Sqrt[Pi]*E^(a+b*x)^2) /;
FreeQ[{a,b},x]


Int[Erfi[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*Erfi[a+b*x]/b - E^(a+b*x)^2/(b*Sqrt[Pi]) /;
FreeQ[{a,b},x]


Int[Erf[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*Erf[a+b*x]^2/b -
  4/Sqrt[Pi]*Int[(a+b*x)*Erf[a+b*x]/E^(a+b*x)^2,x] /;
FreeQ[{a,b},x]


Int[Erfc[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*Erfc[a+b*x]^2/b +
  4/Sqrt[Pi]*Int[(a+b*x)*Erfc[a+b*x]/E^(a+b*x)^2,x] /;
FreeQ[{a,b},x]


Int[Erfi[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*Erfi[a+b*x]^2/b -
  4/Sqrt[Pi]*Int[(a+b*x)*E^(a+b*x)^2*Erfi[a+b*x],x] /;
FreeQ[{a,b},x]


Int[Erf[a_.+b_.*x_]^n_,x_Symbol] :=
  Unintegrable[Erf[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]


Int[Erfc[a_.+b_.*x_]^n_,x_Symbol] :=
  Unintegrable[Erfc[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]


Int[Erfi[a_.+b_.*x_]^n_,x_Symbol] :=
  Unintegrable[Erfi[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]


Int[Erf[b_.*x_]/x_,x_Symbol] :=
  2*b*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},-b^2*x^2] /;
FreeQ[b,x]


Int[Erfc[b_.*x_]/x_,x_Symbol] :=
  Log[x] - Int[Erf[b*x]/x,x] /;
FreeQ[b,x]


Int[Erfi[b_.*x_]/x_,x_Symbol] :=
  2*b*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},b^2*x^2] /;
FreeQ[b,x]


Int[(c_.+d_.*x_)^m_.*Erf[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Erf[a+b*x]/(d*(m+1)) -
  2*b/(Sqrt[Pi]*d*(m+1))*Int[(c+d*x)^(m+1)/E^(a+b*x)^2,x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[(c_.+d_.*x_)^m_.*Erfc[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Erfc[a+b*x]/(d*(m+1)) +
  2*b/(Sqrt[Pi]*d*(m+1))*Int[(c+d*x)^(m+1)/E^(a+b*x)^2,x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[(c_.+d_.*x_)^m_.*Erfi[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Erfi[a+b*x]/(d*(m+1)) -
  2*b/(Sqrt[Pi]*d*(m+1))*Int[(c+d*x)^(m+1)*E^(a+b*x)^2,x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[x_^m_.*Erf[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*Erf[b*x]^2/(m+1) -
  4*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)*E^(-b^2*x^2)*Erf[b*x],x] /;
FreeQ[b,x] && (IGtQ[m,0] || ILtQ[(m+1)/2,0])


Int[x_^m_.*Erfc[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*Erfc[b*x]^2/(m+1) +
  4*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)*E^(-b^2*x^2)*Erfc[b*x],x] /;
FreeQ[b,x] && (IGtQ[m,0] || ILtQ[(m+1)/2,0])


Int[x_^m_.*Erfi[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*Erfi[b*x]^2/(m+1) -
  4*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)*E^(b^2*x^2)*Erfi[b*x],x] /;
FreeQ[b,x] && (IGtQ[m,0] || ILtQ[(m+1)/2,0])


Int[(c_.+d_.*x_)^m_.*Erf[a_+b_.*x_]^2,x_Symbol] :=
  1/b^(m+1)*Subst[Int[ExpandIntegrand[Erf[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*Erfc[a_+b_.*x_]^2,x_Symbol] :=
  1/b^(m+1)*Subst[Int[ExpandIntegrand[Erfc[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*Erfi[a_+b_.*x_]^2,x_Symbol] :=
  1/b^(m+1)*Subst[Int[ExpandIntegrand[Erfi[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*Erf[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(c+d*x)^m*Erf[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(c_.+d_.*x_)^m_.*Erfc[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(c+d*x)^m*Erfc[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(c_.+d_.*x_)^m_.*Erfi[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(c+d*x)^m*Erfi[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[E^(c_.+d_.*x_^2)*Erf[b_.*x_]^n_.,x_Symbol] :=
  E^c*Sqrt[Pi]/(2*b)*Subst[Int[x^n,x],x,Erf[b*x]] /;
FreeQ[{b,c,d,n},x] && EqQ[d,-b^2]


Int[E^(c_.+d_.*x_^2)*Erfc[b_.*x_]^n_.,x_Symbol] :=
  -E^c*Sqrt[Pi]/(2*b)*Subst[Int[x^n,x],x,Erfc[b*x]] /;
FreeQ[{b,c,d,n},x] && EqQ[d,-b^2]


Int[E^(c_.+d_.*x_^2)*Erfi[b_.*x_]^n_.,x_Symbol] :=
  E^c*Sqrt[Pi]/(2*b)*Subst[Int[x^n,x],x,Erfi[b*x]] /;
FreeQ[{b,c,d,n},x] && EqQ[d,b^2]


Int[E^(c_.+d_.*x_^2)*Erf[b_.*x_],x_Symbol] :=
  b*E^c*x^2/Sqrt[Pi]*HypergeometricPFQ[{1,1},{3/2,2},b^2*x^2] /;
FreeQ[{b,c,d},x] && EqQ[d,b^2]


Int[E^(c_.+d_.*x_^2)*Erfc[b_.*x_],x_Symbol] :=
  Int[E^(c+d*x^2),x] - Int[E^(c+d*x^2)*Erf[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d,b^2]


Int[E^(c_.+d_.*x_^2)*Erfi[b_.*x_],x_Symbol] :=
  b*E^c*x^2/Sqrt[Pi]*HypergeometricPFQ[{1,1},{3/2,2},-b^2*x^2] /;
FreeQ[{b,c,d},x] && EqQ[d,-b^2]


Int[E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[E^(c+d*x^2)*Erf[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[E^(c+d*x^2)*Erfc[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[E^(c+d*x^2)*Erfi[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[x_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
  E^(c+d*x^2)*Erf[a+b*x]/(2*d) - 
  b/(d*Sqrt[Pi])*Int[E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] /;
FreeQ[{a,b,c,d},x]


Int[x_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
  E^(c+d*x^2)*Erfc[a+b*x]/(2*d) + 
  b/(d*Sqrt[Pi])*Int[E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] /;
FreeQ[{a,b,c,d},x]


Int[x_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
  E^(c+d*x^2)*Erfi[a+b*x]/(2*d) - 
  b/(d*Sqrt[Pi])*Int[E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] /;
FreeQ[{a,b,c,d},x]


Int[x_^m_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
  x^(m-1)*E^(c+d*x^2)*Erf[a+b*x]/(2*d) - 
  b/(d*Sqrt[Pi])*Int[x^(m-1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] - 
  (m-1)/(2*d)*Int[x^(m-2)*E^(c+d*x^2)*Erf[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,1]


Int[x_^m_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
  x^(m-1)*E^(c+d*x^2)*Erfc[a+b*x]/(2*d) + 
  b/(d*Sqrt[Pi])*Int[x^(m-1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] - 
  (m-1)/(2*d)*Int[x^(m-2)*E^(c+d*x^2)*Erfc[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,1]


Int[x_^m_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
  x^(m-1)*E^(c+d*x^2)*Erfi[a+b*x]/(2*d) - 
  b/(d*Sqrt[Pi])*Int[x^(m-1)*E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] - 
  (m-1)/(2*d)*Int[x^(m-2)*E^(c+d*x^2)*Erfi[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,1]


Int[E^(c_.+d_.*x_^2)*Erf[b_.*x_]/x_,x_Symbol] :=
  2*b*E^c*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1},{3/2,3/2},b^2*x^2] /;
FreeQ[{b,c,d},x] && EqQ[d,b^2]


Int[E^(c_.+d_.*x_^2)*Erfc[b_.*x_]/x_,x_Symbol] :=
  Int[E^(c+d*x^2)/x,x] - Int[E^(c+d*x^2)*Erf[b*x]/x,x] /;
FreeQ[{b,c,d},x] && EqQ[d,b^2]


Int[E^(c_.+d_.*x_^2)*Erfi[b_.*x_]/x_,x_Symbol] :=
  2*b*E^c*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1},{3/2,3/2},-b^2*x^2] /;
FreeQ[{b,c,d},x] && EqQ[d,-b^2]


Int[x_^m_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*E^(c+d*x^2)*Erf[a+b*x]/(m+1) - 
  2*b/((m+1)*Sqrt[Pi])*Int[x^(m+1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] - 
  2*d/(m+1)*Int[x^(m+2)*E^(c+d*x^2)*Erf[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[m,-1]


Int[x_^m_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*E^(c+d*x^2)*Erfc[a+b*x]/(m+1) + 
  2*b/((m+1)*Sqrt[Pi])*Int[x^(m+1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] - 
  2*d/(m+1)*Int[x^(m+2)*E^(c+d*x^2)*Erfc[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[m,-1]


Int[x_^m_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*E^(c+d*x^2)*Erfi[a+b*x]/(m+1) - 
  2*b/((m+1)*Sqrt[Pi])*Int[x^(m+1)*E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] - 
  2*d/(m+1)*Int[x^(m+2)*E^(c+d*x^2)*Erfi[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[m,-1]


Int[(e_.*x_)^m_.*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(e*x)^m*E^(c+d*x^2)*Erf[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(e_.*x_)^m_.*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(e*x)^m*E^(c+d*x^2)*Erfc[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(e_.*x_)^m_.*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(e*x)^m*E^(c+d*x^2)*Erfi[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[Erf[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*Erf[d*(a+b*Log[c*x^n])] - 2*b*d*n/(Sqrt[Pi])*Int[1/E^(d*(a+b*Log[c*x^n]))^2,x] /;
FreeQ[{a,b,c,d,n},x]


Int[Erfc[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*Erfc[d*(a+b*Log[c*x^n])] + 2*b*d*n/(Sqrt[Pi])*Int[1/E^(d*(a+b*Log[c*x^n]))^2,x] /;
FreeQ[{a,b,c,d,n},x]


Int[Erfi[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*Erfi[d*(a+b*Log[c*x^n])] - 2*b*d*n/(Sqrt[Pi])*Int[E^(d*(a+b*Log[c*x^n]))^2,x] /;
FreeQ[{a,b,c,d,n},x]


Int[F_[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
  1/n*Subst[F[d*(a+b*x)],x,Log[c*x^n]] /;
FreeQ[{a,b,c,d,n},x] && MemberQ[{Erf,Erfc,Erfi},F]


Int[(e_.*x_)^m_.*Erf[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*Erf[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  2*b*d*n/(Sqrt[Pi]*(m+1))*Int[(e*x)^m/E^(d*(a+b*Log[c*x^n]))^2,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]


Int[(e_.*x_)^m_.*Erfc[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*Erfc[d*(a+b*Log[c*x^n])]/(e*(m+1)) + 
  2*b*d*n/(Sqrt[Pi]*(m+1))*Int[(e*x)^m/E^(d*(a+b*Log[c*x^n]))^2,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]


Int[(e_.*x_)^m_.*Erfi[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*Erfi[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  2*b*d*n/(Sqrt[Pi]*(m+1))*Int[(e*x)^m*E^(d*(a+b*Log[c*x^n]))^2,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]


Int[Sin[c_.+d_.*x_^2]*Erf[b_.*x_],x_Symbol] :=
  I/2*Int[E^(-I*c-I*d*x^2)*Erf[b*x],x] - I/2*Int[E^(I*c+I*d*x^2)*Erf[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]


Int[Sin[c_.+d_.*x_^2]*Erfc[b_.*x_],x_Symbol] :=
  I/2*Int[E^(-I*c-I*d*x^2)*Erfc[b*x],x] - I/2*Int[E^(I*c+I*d*x^2)*Erfc[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]


Int[Sin[c_.+d_.*x_^2]*Erfi[b_.*x_],x_Symbol] :=
  I/2*Int[E^(-I*c-I*d*x^2)*Erfi[b*x],x] - I/2*Int[E^(I*c+I*d*x^2)*Erfi[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]


Int[Cos[c_.+d_.*x_^2]*Erf[b_.*x_],x_Symbol] :=
  1/2*Int[E^(-I*c-I*d*x^2)*Erf[b*x],x] + 1/2*Int[E^(I*c+I*d*x^2)*Erf[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]


Int[Cos[c_.+d_.*x_^2]*Erfc[b_.*x_],x_Symbol] :=
  1/2*Int[E^(-I*c-I*d*x^2)*Erfc[b*x],x] + 1/2*Int[E^(I*c+I*d*x^2)*Erfc[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]


Int[Cos[c_.+d_.*x_^2]*Erfi[b_.*x_],x_Symbol] :=
  1/2*Int[E^(-I*c-I*d*x^2)*Erfi[b*x],x] + 1/2*Int[E^(I*c+I*d*x^2)*Erfi[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]


Int[Sinh[c_.+d_.*x_^2]*Erf[b_.*x_],x_Symbol] :=
  1/2*Int[E^(c+d*x^2)*Erf[b*x],x] - 1/2*Int[E^(-c-d*x^2)*Erf[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,b^4]


Int[Sinh[c_.+d_.*x_^2]*Erfc[b_.*x_],x_Symbol] :=
  1/2*Int[E^(c+d*x^2)*Erfc[b*x],x] - 1/2*Int[E^(-c-d*x^2)*Erfc[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,b^4]


Int[Sinh[c_.+d_.*x_^2]*Erfi[b_.*x_],x_Symbol] :=
  1/2*Int[E^(c+d*x^2)*Erfi[b*x],x] - 1/2*Int[E^(-c-d*x^2)*Erfi[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,b^4]


Int[Cosh[c_.+d_.*x_^2]*Erf[b_.*x_],x_Symbol] :=
  1/2*Int[E^(c+d*x^2)*Erf[b*x],x] + 1/2*Int[E^(-c-d*x^2)*Erf[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,b^4]


Int[Cosh[c_.+d_.*x_^2]*Erfc[b_.*x_],x_Symbol] :=
  1/2*Int[E^(c+d*x^2)*Erfc[b*x],x] + 1/2*Int[E^(-c-d*x^2)*Erfc[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,b^4]


Int[Cosh[c_.+d_.*x_^2]*Erfi[b_.*x_],x_Symbol] :=
  1/2*Int[E^(c+d*x^2)*Erfi[b*x],x] + 1/2*Int[E^(-c-d*x^2)*Erfi[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,b^4]


Int[F_[f_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])],x_Symbol] :=
  1/e*Subst[Int[F[f*(a+b*Log[c*x^n])],x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,n},x] && MemberQ[{Erf,Erfc,Erfi,FresnelS,FresnelC,ExpIntegralEi,SinIntegral,CosIntegral,SinhIntegral,CoshIntegral},F]


Int[(g_+h_. x_)^m_.*F_[f_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])],x_Symbol] :=
  1/e*Subst[Int[(g*x/d)^m*F[f*(a+b*Log[c*x^n])],x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && EqQ[e*f-d*g,0] && 
  MemberQ[{Erf,Erfc,Erfi,FresnelS,FresnelC,ExpIntegralEi,SinIntegral,CosIntegral,SinhIntegral,CoshIntegral},F]





(* ::Subsection::Closed:: *)
(*8.2 Fresnel integral functions*)


Int[FresnelS[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*FresnelS[a+b*x]/b + Cos[Pi/2*(a+b*x)^2]/(b*Pi) /;
FreeQ[{a,b},x]


Int[FresnelC[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*FresnelC[a+b*x]/b - Sin[Pi/2*(a+b*x)^2]/(b*Pi) /;
FreeQ[{a,b},x]


Int[FresnelS[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*FresnelS[a+b*x]^2/b -
  2*Int[(a+b*x)*Sin[Pi/2*(a+b*x)^2]*FresnelS[a+b*x],x] /;
FreeQ[{a,b},x]


Int[FresnelC[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*FresnelC[a+b*x]^2/b -
  2*Int[(a+b*x)*Cos[Pi/2*(a+b*x)^2]*FresnelC[a+b*x],x] /;
FreeQ[{a,b},x]


Int[FresnelS[a_.+b_.*x_]^n_,x_Symbol] :=
  Unintegrable[FresnelS[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]


Int[FresnelC[a_.+b_.*x_]^n_,x_Symbol] :=
  Unintegrable[FresnelC[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]


Int[FresnelS[b_.*x_]/x_,x_Symbol] :=
  (1+I)/4*Int[Erf[Sqrt[Pi]/2*(1+I)*b*x]/x,x] + (1-I)/4*Int[Erf[Sqrt[Pi]/2*(1-I)*b*x]/x,x] /;
FreeQ[b,x]


Int[FresnelC[b_.*x_]/x_,x_Symbol] :=
  (1-I)/4*Int[Erf[Sqrt[Pi]/2*(1+I)*b*x]/x,x] + (1+I)/4*Int[Erf[Sqrt[Pi]/2*(1-I)*b*x]/x,x] /;
FreeQ[b,x]


Int[(d_.*x_)^m_.*FresnelS[b_.*x_],x_Symbol] :=
  (d*x)^(m+1)*FresnelS[b*x]/(d*(m+1)) - b/(d*(m+1))*Int[(d*x)^(m+1)*Sin[Pi/2*b^2*x^2],x] /;
FreeQ[{b,d,m},x] && NeQ[m,-1]


Int[(d_.*x_)^m_.*FresnelC[b_.*x_],x_Symbol] :=
  (d*x)^(m+1)*FresnelC[b*x]/(d*(m+1)) - b/(d*(m+1))*Int[(d*x)^(m+1)*Cos[Pi/2*b^2*x^2],x] /;
FreeQ[{b,d,m},x] && NeQ[m,-1]


Int[(c_.+d_.*x_)^m_.*FresnelS[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*FresnelS[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Sin[Pi/2*(a+b*x)^2],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*FresnelC[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*FresnelC[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Cos[Pi/2*(a+b*x)^2],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[x_^m_.*FresnelS[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*FresnelS[b*x]^2/(m+1) -
  2*b/(m+1)*Int[x^(m+1)*Sin[Pi/2*b^2*x^2]*FresnelS[b*x],x] /;
FreeQ[b,x] && IntegerQ[m] && NeQ[m,-1]


Int[x_^m_.*FresnelC[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*FresnelC[b*x]^2/(m+1) -
  2*b/(m+1)*Int[x^(m+1)*Cos[Pi/2*b^2*x^2]*FresnelC[b*x],x] /;
FreeQ[b,x] && IntegerQ[m] && NeQ[m,-1]


Int[(c_.+d_.*x_)^m_.*FresnelS[a_+b_.*x_]^2,x_Symbol] :=
  1/b^(m+1)*Subst[Int[ExpandIntegrand[FresnelS[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*FresnelC[a_+b_.*x_]^2,x_Symbol] :=
  1/b^(m+1)*Subst[Int[ExpandIntegrand[FresnelC[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(c+d*x)^m*FresnelS[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(c_.+d_.*x_)^m_.*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(c+d*x)^m*FresnelC[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[E^(c_.+d_.*x_^2)*FresnelS[b_.*x_],x_Symbol] :=
  (1+I)/4*Int[E^(c+d*x^2)*Erf[Sqrt[Pi]/2*(1+I)*b*x],x] + (1-I)/4*Int[E^(c+d*x^2)*Erf[Sqrt[Pi]/2*(1-I)*b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,-Pi^2/4*b^4]


Int[E^(c_.+d_.*x_^2)*FresnelC[b_.*x_],x_Symbol] :=
  (1-I)/4*Int[E^(c+d*x^2)*Erf[Sqrt[Pi]/2*(1+I)*b*x],x] + (1+I)/4*Int[E^(c+d*x^2)*Erf[Sqrt[Pi]/2*(1-I)*b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,-Pi^2/4*b^4]


Int[E^(c_.+d_.*x_^2)*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[E^(c+d*x^2)*FresnelS[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[E^(c_.+d_.*x_^2)*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[E^(c+d*x^2)*FresnelC[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[Sin[d_.*x_^2]*FresnelS[b_.*x_]^n_.,x_Symbol] :=
  Pi*b/(2*d)*Subst[Int[x^n,x],x,FresnelS[b*x]] /;
FreeQ[{b,d,n},x] && EqQ[d^2,Pi^2/4*b^4]


Int[Cos[d_.*x_^2]*FresnelC[b_.*x_]^n_.,x_Symbol] :=
  Pi*b/(2*d)*Subst[Int[x^n,x],x,FresnelC[b*x]] /;
FreeQ[{b,d,n},x] && EqQ[d^2,Pi^2/4*b^4]


Int[Sin[c_+d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  Sin[c]*Int[Cos[d*x^2]*FresnelS[b*x],x] + Cos[c]*Int[Sin[d*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[Cos[c_+d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  Cos[c]*Int[Cos[d*x^2]*FresnelC[b*x],x] - Sin[c]*Int[Sin[d*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[Sin[c_.+d_.*x_^2]*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[Sin[c+d*x^2]*FresnelS[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[Cos[c_.+d_.*x_^2]*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[Cos[c+d*x^2]*FresnelC[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[Cos[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  FresnelC[b*x]*FresnelS[b*x]/(2*b) - 
  1/8*I*b*x^2*HypergeometricPFQ[{1,1},{3/2,2},-1/2*I*b^2*Pi*x^2] + 
  1/8*I*b*x^2*HypergeometricPFQ[{1,1},{3/2,2},1/2*I*b^2*Pi*x^2] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[Sin[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  b*Pi*FresnelC[b*x]*FresnelS[b*x]/(4*d) + 
  1/8*I*b*x^2*HypergeometricPFQ[{1,1},{3/2,2},-I*d*x^2] - 
  1/8*I*b*x^2*HypergeometricPFQ[{1,1},{3/2,2},I*d*x^2] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[Cos[c_+d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  Cos[c]*Int[Cos[d*x^2]*FresnelS[b*x],x] - Sin[c]*Int[Sin[d*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[Sin[c_+d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  Sin[c]*Int[Cos[d*x^2]*FresnelC[b*x],x] + Cos[c]*Int[Sin[d*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,c,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[Cos[c_.+d_.*x_^2]*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[Cos[c+d*x^2]*FresnelS[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[Sin[c_.+d_.*x_^2]*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[Sin[c+d*x^2]*FresnelC[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[x_*Sin[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  -Cos[d*x^2]*FresnelS[b*x]/(2*d) + 1/(2*b*Pi)*Int[Sin[2*d*x^2],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[x_*Cos[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  Sin[d*x^2]*FresnelC[b*x]/(2*d) - b/(4*d)*Int[Sin[2*d*x^2],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[x_^m_*Sin[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  -x^(m-1)*Cos[d*x^2]*FresnelS[b*x]/(2*d) + 
  1/(2*b*Pi)*Int[x^(m-1)*Sin[2*d*x^2],x] + 
  (m-1)/(2*d)*Int[x^(m-2)*Cos[d*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && IGtQ[m,1]


Int[x_^m_*Cos[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  x^(m-1)*Sin[d*x^2]*FresnelC[b*x]/(2*d) - 
  b/(4*d)*Int[x^(m-1)*Sin[2*d*x^2],x] - 
  (m-1)/(2*d)*Int[x^(m-2)*Sin[d*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && IGtQ[m,1]


Int[x_^m_*Sin[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  x^(m+1)*Sin[d*x^2]*FresnelS[b*x]/(m+1) - 
  d*x^(m+2)/(Pi*b*(m+1)*(m+2)) + 
  d/(Pi*b*(m+1))*Int[x^(m+1)*Cos[2*d*x^2],x] - 
  2*d/(m+1)*Int[x^(m+2)*Cos[d*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && ILtQ[m,-2]


Int[x_^m_*Cos[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  x^(m+1)*Cos[d*x^2]*FresnelC[b*x]/(m+1) - 
  b*x^(m+2)/(2*(m+1)*(m+2)) - 
  b/(2*(m+1))*Int[x^(m+1)*Cos[2*d*x^2],x] + 
  2*d/(m+1)*Int[x^(m+2)*Sin[d*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && ILtQ[m,-2]


Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^2]*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(e*x)^m*Sin[c+d*x^2]*FresnelS[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^2]*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(e*x)^m*Cos[c+d*x^2]*FresnelC[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[x_*Cos[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  Sin[d*x^2]*FresnelS[b*x]/(2*d) - 1/(Pi*b)*Int[Sin[d*x^2]^2,x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[x_*Sin[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  -Cos[d*x^2]*FresnelC[b*x]/(2*d) + b/(2*d)*Int[Cos[d*x^2]^2,x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]


Int[x_^m_*Cos[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  x^(m-1)*Sin[d*x^2]*FresnelS[b*x]/(2*d) - 
  1/(Pi*b)*Int[x^(m-1)*Sin[d*x^2]^2,x] - 
  (m-1)/(2*d)*Int[x^(m-2)*Sin[d*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && IGtQ[m,1]


Int[x_^m_*Sin[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  -x^(m-1)*Cos[d*x^2]*FresnelC[b*x]/(2*d) + 
  b/(2*d)*Int[x^(m-1)*Cos[d*x^2]^2,x] + 
  (m-1)/(2*d)*Int[x^(m-2)*Cos[d*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && IGtQ[m,1]


Int[x_^m_*Cos[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  x^(m+1)*Cos[d*x^2]*FresnelS[b*x]/(m+1) - 
  d/(Pi*b*(m+1))*Int[x^(m+1)*Sin[2*d*x^2],x] + 
  2*d/(m+1)*Int[x^(m+2)*Sin[d*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && ILtQ[m,-1]


Int[x_^m_*Sin[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  x^(m+1)*Sin[d*x^2]*FresnelC[b*x]/(m+1) - 
  b/(2*(m+1))*Int[x^(m+1)*Sin[2*d*x^2],x] - 
  2*d/(m+1)*Int[x^(m+2)*Cos[d*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && ILtQ[m,-1]


Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^2]*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(e*x)^m*Cos[c+d*x^2]*FresnelS[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^2]*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
  Unintegrable[(e*x)^m*Sin[c+d*x^2]*FresnelC[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[FresnelS[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*FresnelS[d*(a+b*Log[c*x^n])] - b*d*n*Int[Sin[Pi/2*(d*(a+b*Log[c*x^n]))^2],x] /;
FreeQ[{a,b,c,d,n},x]


Int[FresnelC[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*FresnelC[d*(a+b*Log[c*x^n])] - b*d*n*Int[Cos[Pi/2*(d*(a+b*Log[c*x^n]))^2],x] /;
FreeQ[{a,b,c,d,n},x]


Int[F_[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
  1/n*Subst[F[d*(a+b*x)],x,Log[c*x^n]] /;
FreeQ[{a,b,c,d,n},x] && MemberQ[{FresnelS,FresnelC},F]


Int[(e_.*x_)^m_.*FresnelS[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*FresnelS[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  b*d*n/(m+1)*Int[(e*x)^m*Sin[Pi/2*(d*(a+b*Log[c*x^n]))^2],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]


Int[(e_.*x_)^m_.*FresnelC[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*FresnelC[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  b*d*n/(m+1)*Int[(e*x)^m*Cos[Pi/2*(d*(a+b*Log[c*x^n]))^2],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]





(* ::Subsection::Closed:: *)
(*8.3 Exponential integral functions*)


Int[ExpIntegralE[n_,a_.+b_.*x_],x_Symbol] :=
  -ExpIntegralE[n+1,a+b*x]/b /;
FreeQ[{a,b,n},x]


Int[x_^m_.*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
  -x^m*ExpIntegralE[n+1,b*x]/b + 
  m/b*Int[x^(m-1)*ExpIntegralE[n+1,b*x],x] /;
FreeQ[b,x] && EqQ[m+n,0] && IGtQ[m,0]


Int[ExpIntegralE[1,b_.*x_]/x_,x_Symbol] :=
  b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] - EulerGamma*Log[x] - 1/2*Log[b*x]^2 /;
FreeQ[b,x]


Int[x_^m_*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
  x^(m+1)*ExpIntegralE[n,b*x]/(m+1) +
  b/(m+1)*Int[x^(m+1)*ExpIntegralE[n-1,b*x],x] /;
FreeQ[b,x] && EqQ[m+n,0] && ILtQ[m,-1]


Int[(d_.*x_)^m_*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
  (d*x)^m*Gamma[m+1]*Log[x]/(b*(b*x)^m) - (d*x)^(m+1)*HypergeometricPFQ[{m+1,m+1},{m+2,m+2},-b*x]/(d*(m+1)^2) /;
FreeQ[{b,d,m,n},x] && EqQ[m+n,0] && Not[IntegerQ[m]]


Int[(d_.*x_)^m_.*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
  (d*x)^(m+1)*ExpIntegralE[n,b*x]/(d*(m+n)) - (d*x)^(m+1)*ExpIntegralE[-m,b*x]/(d*(m+n)) /;
FreeQ[{b,d,m,n},x] && NeQ[m+n,0]


Int[(c_.+d_.*x_)^m_.*ExpIntegralE[n_,a_+b_.*x_],x_Symbol] :=
  -(c+d*x)^m*ExpIntegralE[n+1,a+b*x]/b +
  d*m/b*Int[(c+d*x)^(m-1)*ExpIntegralE[n+1,a+b*x],x] /;
FreeQ[{a,b,c,d,m,n},x] && (IGtQ[m,0] || ILtQ[n,0] || GtQ[m,0] && LtQ[n,-1])


Int[(c_.+d_.*x_)^m_.*ExpIntegralE[n_,a_+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*ExpIntegralE[n,a+b*x]/(d*(m+1)) +
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*ExpIntegralE[n-1,a+b*x],x] /;
FreeQ[{a,b,c,d,m,n},x] && (IGtQ[n,0] || LtQ[m,-1] && GtQ[n,0]) && NeQ[m,-1]


Int[(c_.+d_.*x_)^m_.*ExpIntegralE[n_,a_+b_.*x_],x_Symbol] :=
  Unintegrable[(c+d*x)^m*ExpIntegralE[n,a+b*x],x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[ExpIntegralEi[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*ExpIntegralEi[a+b*x]/b - E^(a+b*x)/b /;
FreeQ[{a,b},x]


Int[ExpIntegralEi[b_.*x_]/x_,x_Symbol] :=
  Log[x]*(ExpIntegralEi[b*x]+ExpIntegralE[1,-b*x]) - Int[ExpIntegralE[1,-b*x]/x,x] /;
FreeQ[b,x]


Int[ExpIntegralEi[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Unintegrable[ExpIntegralEi[a+b*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[(c_.+d_.*x_)^m_.*ExpIntegralEi[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*ExpIntegralEi[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*E^(a+b*x)/(a+b*x),x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[ExpIntegralEi[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*ExpIntegralEi[a+b*x]^2/b -
  2*Int[E^(a+b*x)*ExpIntegralEi[a+b*x],x] /;
FreeQ[{a,b},x]


Int[x_^m_.*ExpIntegralEi[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*ExpIntegralEi[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*E^(b*x)*ExpIntegralEi[b*x],x] /;
FreeQ[b,x] && IGtQ[m,0]


Int[x_^m_.*ExpIntegralEi[a_+b_.*x_]^2,x_Symbol] :=
  x^(m+1)*ExpIntegralEi[a+b*x]^2/(m+1) +
  a*x^m*ExpIntegralEi[a+b*x]^2/(b*(m+1)) -
  2/(m+1)*Int[x^m*E^(a+b*x)*ExpIntegralEi[a+b*x],x] -
  a*m/(b*(m+1))*Int[x^(m-1)*ExpIntegralEi[a+b*x]^2,x] /;
FreeQ[{a,b},x] && IGtQ[m,0]


(* Int[x_^m_.*ExpIntegralEi[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*ExpIntegralEi[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*ExpIntegralEi[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*E^(a+b*x)*ExpIntegralEi[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*ExpIntegralEi[a+b*x]^2,x] /;
FreeQ[{a,b},x] && ILtQ[m,-2] *)


Int[E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
  E^(a+b*x)*ExpIntegralEi[c+d*x]/b -
  d/b*Int[E^(a+c+(b+d)*x)/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[x_^m_.*E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
  x^m*E^(a+b*x)*ExpIntegralEi[c+d*x]/b -
  d/b*Int[x^m*E^(a+c+(b+d)*x)/(c+d*x),x] -
  m/b*Int[x^(m-1)*E^(a+b*x)*ExpIntegralEi[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[x_^m_*E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*E^(a+b*x)*ExpIntegralEi[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*E^(a+c+(b+d)*x)/(c+d*x),x] -
  b/(m+1)*Int[x^(m+1)*E^(a+b*x)*ExpIntegralEi[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[m,-1]


Int[ExpIntegralEi[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*ExpIntegralEi[d*(a+b*Log[c*x^n])] - b*n*E^(a*d)*Int[(c*x^n)^(b*d)/(a+b*Log[c*x^n]),x] /;
FreeQ[{a,b,c,d,n},x]


Int[ExpIntegralEi[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
  1/n*Subst[ExpIntegralEi[d*(a+b*x)],x,Log[c*x^n]] /;
FreeQ[{a,b,c,d,n},x]


Int[(e_.*x_)^m_.*ExpIntegralEi[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*ExpIntegralEi[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  b*n*E^(a*d)*(c*x^n)^(b*d)/((m+1)*(e*x)^(b*d*n))*Int[(e*x)^(m+b*d*n)/(a+b*Log[c*x^n]),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]


Int[LogIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*LogIntegral[a+b*x]/b - ExpIntegralEi[2*Log[a+b*x]]/b /;
FreeQ[{a,b},x]


Int[LogIntegral[b_.*x_]/x_,x_Symbol] :=
  -b*x + Log[b*x]*LogIntegral[b*x] /;
FreeQ[b,x]


Int[LogIntegral[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Unintegrable[LogIntegral[a+b*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[(c_.+d_.*x_)^m_.*LogIntegral[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*LogIntegral[a+b*x]/(d*(m+1)) - b/(d*(m+1))*Int[(c+d*x)^(m+1)/Log[a+b*x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]





(* ::Subsection::Closed:: *)
(*8.4 Trig integral functions*)


Int[SinIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*SinIntegral[a+b*x]/b + Cos[a+b*x]/b/;
FreeQ[{a,b},x]


Int[CosIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*CosIntegral[a+b*x]/b - Sin[a+b*x]/b /;
FreeQ[{a,b},x]


Int[SinIntegral[b_.*x_]/x_,x_Symbol] :=
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-I*b*x] + 
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},I*b*x] /;
FreeQ[b,x]


Int[CosIntegral[b_.*x_]/x_,x_Symbol] :=
  -1/2*I*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-I*b*x] + 
  1/2*I*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},I*b*x] + 
  EulerGamma*Log[x] + 
  1/2*Log[b*x]^2 /;
FreeQ[b,x]


Int[(c_.+d_.*x_)^m_.*SinIntegral[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*SinIntegral[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Sin[a+b*x]/(a+b*x),x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[(c_.+d_.*x_)^m_.*CosIntegral[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*CosIntegral[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Cos[a+b*x]/(a+b*x),x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[SinIntegral[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*SinIntegral[a+b*x]^2/b -
  2*Int[Sin[a+b*x]*SinIntegral[a+b*x],x] /;
FreeQ[{a,b},x]


Int[CosIntegral[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*CosIntegral[a+b*x]^2/b -
  2*Int[Cos[a+b*x]*CosIntegral[a+b*x],x] /;
FreeQ[{a,b},x]


Int[x_^m_.*SinIntegral[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*SinIntegral[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*Sin[b*x]*SinIntegral[b*x],x] /;
FreeQ[b,x] && IGtQ[m,0]


Int[x_^m_.*CosIntegral[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*CosIntegral[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*Cos[b*x]*CosIntegral[b*x],x] /;
FreeQ[b,x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*SinIntegral[a_+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*(c+d*x)^m*SinIntegral[a+b*x]^2/(b*(m+1)) - 
  2/(m+1)*Int[(c+d*x)^m*Sin[a+b*x]*SinIntegral[a+b*x],x] + 
  (b*c-a*d)*m/(b*(m+1))*Int[(c+d*x)^(m-1)*SinIntegral[a+b*x]^2,x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*CosIntegral[a_+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*(c+d*x)^m*CosIntegral[a+b*x]^2/(b*(m+1)) - 
  2/(m+1)*Int[(c+d*x)^m*Cos[a+b*x]*CosIntegral[a+b*x],x] + 
  (b*c-a*d)*m/(b*(m+1))*Int[(c+d*x)^(m-1)*CosIntegral[a+b*x]^2,x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


(* Int[x_^m_.*SinIntegral[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*SinIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*SinIntegral[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*Sin[a+b*x]*SinIntegral[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*SinIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && ILtQ[m,-2] *)


(* Int[x_^m_.*CosIntegral[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*CosIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*CosIntegral[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*Cos[a+b*x]*CosIntegral[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*CosIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && ILtQ[m,-2] *)


Int[Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  -Cos[a+b*x]*SinIntegral[c+d*x]/b +
  d/b*Int[Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  Sin[a+b*x]*CosIntegral[c+d*x]/b -
  d/b*Int[Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  -(e+f*x)^m*Cos[a+b*x]*SinIntegral[c+d*x]/b +
  d/b*Int[(e+f*x)^m*Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] +
  f*m/b*Int[(e+f*x)^(m-1)*Cos[a+b*x]*SinIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^m*Sin[a+b*x]*CosIntegral[c+d*x]/b -
  d/b*Int[(e+f*x)^m*Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] -
  f*m/b*Int[(e+f*x)^(m-1)*Sin[a+b*x]*CosIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_*Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^(m+1)*Sin[a+b*x]*SinIntegral[c+d*x]/(f*(m+1)) -
  d/(f*(m+1))*Int[(e+f*x)^(m+1)*Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] -
  b/(f*(m+1))*Int[(e+f*x)^(m+1)*Cos[a+b*x]*SinIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]


Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^(m+1)*Cos[a+b*x]*CosIntegral[c+d*x]/(f*(m+1)) -
  d/(f*(m+1))*Int[(e+f*x)^(m+1)*Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] +
  b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sin[a+b*x]*CosIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]


Int[Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  Sin[a+b*x]*SinIntegral[c+d*x]/b -
  d/b*Int[Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  -Cos[a+b*x]*CosIntegral[c+d*x]/b +
  d/b*Int[Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^m*Sin[a+b*x]*SinIntegral[c+d*x]/b -
  d/b*Int[(e+f*x)^m*Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] -
  f*m/b*Int[(e+f*x)^(m-1)*Sin[a+b*x]*SinIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  -(e+f*x)^m*Cos[a+b*x]*CosIntegral[c+d*x]/b +
  d/b*Int[(e+f*x)^m*Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] +
  f*m/b*Int[(e+f*x)^(m-1)*Cos[a+b*x]*CosIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^(m+1)*Cos[a+b*x]*SinIntegral[c+d*x]/(f*(m+1)) -
  d/(f*(m+1))*Int[(e+f*x)^(m+1)*Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] +
  b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sin[a+b*x]*SinIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]


Int[(e_.+f_.*x_)^m_*Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^(m+1)*Sin[a+b*x]*CosIntegral[c+d*x]/(f*(m+1)) -
  d/(f*(m+1))*Int[(e+f*x)^(m+1)*Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] -
  b/(f*(m+1))*Int[(e+f*x)^(m+1)*Cos[a+b*x]*CosIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]


Int[SinIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*SinIntegral[d*(a+b*Log[c*x^n])] - b*d*n*Int[Sin[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
FreeQ[{a,b,c,d,n},x]


Int[CosIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*CosIntegral[d*(a+b*Log[c*x^n])] - b*d*n*Int[Cos[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
FreeQ[{a,b,c,d,n},x]


Int[F_[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
  1/n*Subst[F[d*(a+b*x)],x,Log[c*x^n]] /;
FreeQ[{a,b,c,d,n},x] && MemberQ[{SinIntegral,CosIntegral},x]


Int[(e_.*x_)^m_.*SinIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*SinIntegral[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  b*d*n/(m+1)*Int[(e*x)^m*Sin[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]


Int[(e_.*x_)^m_.*CosIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*CosIntegral[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  b*d*n/(m+1)*Int[(e*x)^m*Cos[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]





(* ::Subsection::Closed:: *)
(*8.5 Hyperbolic integral functions*)


Int[SinhIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*SinhIntegral[a+b*x]/b - Cosh[a+b*x]/b/;
FreeQ[{a,b},x]


Int[CoshIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*CoshIntegral[a+b*x]/b - Sinh[a+b*x]/b /;
FreeQ[{a,b},x]


Int[SinhIntegral[b_.*x_]/x_,x_Symbol] :=
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] + 
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},b*x] /;
FreeQ[b,x]


Int[CoshIntegral[b_.*x_]/x_,x_Symbol] :=
  -1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] + 
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},b*x] + 
  EulerGamma*Log[x] + 
  1/2*Log[b*x]^2 /;
FreeQ[b,x]


Int[(c_.+d_.*x_)^m_.*SinhIntegral[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*SinhIntegral[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Sinh[a+b*x]/(a+b*x),x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[(c_.+d_.*x_)^m_.*CoshIntegral[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*CoshIntegral[a+b*x]/(d*(m+1)) - 
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Cosh[a+b*x]/(a+b*x),x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[SinhIntegral[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*SinhIntegral[a+b*x]^2/b -
  2*Int[Sinh[a+b*x]*SinhIntegral[a+b*x],x] /;
FreeQ[{a,b},x]


Int[CoshIntegral[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*CoshIntegral[a+b*x]^2/b -
  2*Int[Cosh[a+b*x]*CoshIntegral[a+b*x],x] /;
FreeQ[{a,b},x]


Int[x_^m_.*SinhIntegral[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*SinhIntegral[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*Sinh[b*x]*SinhIntegral[b*x],x] /;
FreeQ[b,x] && IGtQ[m,0]


Int[x_^m_.*CoshIntegral[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*CoshIntegral[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*Cosh[b*x]*CoshIntegral[b*x],x] /;
FreeQ[b,x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*SinhIntegral[a_+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*(c+d*x)^m*SinhIntegral[a+b*x]^2/(b*(m+1)) - 
  2/(m+1)*Int[(c+d*x)^m*Sinh[a+b*x]*SinhIntegral[a+b*x],x] + 
  (b*c-a*d)*m/(b*(m+1))*Int[(c+d*x)^(m-1)*SinhIntegral[a+b*x]^2,x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*CoshIntegral[a_+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*(c+d*x)^m*CoshIntegral[a+b*x]^2/(b*(m+1)) - 
  2/(m+1)*Int[(c+d*x)^m*Cosh[a+b*x]*CoshIntegral[a+b*x],x] + 
  (b*c-a*d)*m/(b*(m+1))*Int[(c+d*x)^(m-1)*CoshIntegral[a+b*x]^2,x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


(* Int[x_^m_.*SinhIntegral[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*SinhIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*SinhIntegral[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*Sinh[a+b*x]*SinhIntegral[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*SinhIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && ILtQ[m,-2] *)


(* Int[x_^m_.*CoshIntegral[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*CoshIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*CoshIntegral[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*Cosh[a+b*x]*CoshIntegral[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*CoshIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && ILtQ[m,-2] *)


Int[Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  Cosh[a+b*x]*SinhIntegral[c+d*x]/b -
  d/b*Int[Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  Sinh[a+b*x]*CoshIntegral[c+d*x]/b -
  d/b*Int[Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^m*Cosh[a+b*x]*SinhIntegral[c+d*x]/b - 
  d/b*Int[(e+f*x)^m*Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] - 
  f*m/b*Int[(e+f*x)^(m-1)*Cosh[a+b*x]*SinhIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^m*Sinh[a+b*x]*CoshIntegral[c+d*x]/b - 
  d/b*Int[(e+f*x)^m*Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] - 
  f*m/b*Int[(e+f*x)^(m-1)*Sinh[a+b*x]*CoshIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_*Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^(m+1)*Sinh[a+b*x]*SinhIntegral[c+d*x]/(f*(m+1)) - 
  d/(f*(m+1))*Int[(e+f*x)^(m+1)*Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] - 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)*Cosh[a+b*x]*SinhIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]


Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^(m+1)*Cosh[a+b*x]*CoshIntegral[c+d*x]/(f*(m+1)) - 
  d/(f*(m+1))*Int[(e+f*x)^(m+1)*Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] - 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sinh[a+b*x]*CoshIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]


Int[Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  Sinh[a+b*x]*SinhIntegral[c+d*x]/b -
  d/b*Int[Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  Cosh[a+b*x]*CoshIntegral[c+d*x]/b -
  d/b*Int[Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^m*Sinh[a+b*x]*SinhIntegral[c+d*x]/b -
  d/b*Int[(e+f*x)^m*Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
  f*m/b*Int[(e+f*x)^(m-1)*Sinh[a+b*x]*SinhIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^m*Cosh[a+b*x]*CoshIntegral[c+d*x]/b -
  d/b*Int[(e+f*x)^m*Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
  f*m/b*Int[(e+f*x)^(m-1)*Cosh[a+b*x]*CoshIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^(m+1)*Cosh[a+b*x]*SinhIntegral[c+d*x]/(f*(m+1)) -
  d/(f*(m+1))*Int[(e+f*x)^(m+1)*Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
  b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sinh[a+b*x]*SinhIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]


Int[(e_.+f_.*x_)^m_*Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  (e+f*x)^(m+1)*Sinh[a+b*x]*CoshIntegral[c+d*x]/(f*(m+1)) -
  d/(f*(m+1))*Int[(e+f*x)^(m+1)*Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
  b/(f*(m+1))*Int[(e+f*x)^(m+1)*Cosh[a+b*x]*CoshIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]


Int[SinhIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*SinhIntegral[d*(a+b*Log[c*x^n])] - b*d*n*Int[Sinh[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
FreeQ[{a,b,c,d,n},x]


Int[CoshIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*CoshIntegral[d*(a+b*Log[c*x^n])] - b*d*n*Int[Cosh[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
FreeQ[{a,b,c,d,n},x]


Int[F_[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
  1/n*Subst[F[d*(a+b*x)],x,Log[c*x^n]] /;
FreeQ[{a,b,c,d,n},x] && MemberQ[{SinhIntegral,CoshIntegral},x]


Int[(e_.*x_)^m_.*SinhIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*SinhIntegral[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  b*d*n/(m+1)*Int[(e*x)^m*Sinh[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]


Int[(e_.*x_)^m_.*CoshIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*CoshIntegral[d*(a+b*Log[c*x^n])]/(e*(m+1)) - 
  b*d*n/(m+1)*Int[(e*x)^m*Cosh[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]





(* ::Subsection::Closed:: *)
(*8.6 Gamma functions*)


Int[Gamma[n_,a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*Gamma[n,a+b*x]/b - Gamma[n+1,a+b*x]/b /;
FreeQ[{a,b,n},x]


Int[Gamma[0,b_.*x_]/x_,x_Symbol] :=
  b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] - EulerGamma*Log[x] - 1/2*Log[b*x]^2 /;
FreeQ[b,x]


(* Int[Gamma[1,b_.*x_]/x_,x_Symbol] :=
  Int[1/(x*E^(b*x)),x] /;
FreeQ[b,x] *)


Int[Gamma[n_,b_.*x_]/x_,x_Symbol] :=
  -Gamma[n-1,b*x] + (n-1)*Int[Gamma[n-1,b*x]/x,x] /;
FreeQ[b,x] && IGtQ[n,1]


Int[Gamma[n_,b_.*x_]/x_,x_Symbol] :=
  Gamma[n,b*x]/n + 1/n*Int[Gamma[n+1,b*x]/x,x] /;
FreeQ[b,x] && ILtQ[n,0]


Int[Gamma[n_,b_.*x_]/x_,x_Symbol] :=
  Gamma[n]*Log[x] - (b*x)^n/n^2*HypergeometricPFQ[{n,n},{1+n,1+n},-b*x] /;
FreeQ[{b,n},x] && Not[IntegerQ[n]]


Int[(d_.*x_)^m_.*Gamma[n_,b_.*x_],x_Symbol] :=
  (d*x)^(m+1)*Gamma[n,b*x]/(d*(m+1)) - 
  (d*x)^m*Gamma[m+n+1,b*x]/(b*(m+1)*(b*x)^m) /;
FreeQ[{b,d,m,n},x] && NeQ[m,-1]


Int[(c_+d_.*x_)^m_.*Gamma[n_,a_+b_.*x_],x_Symbol] :=
  1/b*Subst[Int[(d*x/b)^m*Gamma[n,x],x],x,a+b*x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[b*c-a*d,0]


Int[Gamma[n_,a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Int[(a+b*x)^(n-1)/((c+d*x)*E^(a+b*x)),x] + (n-1)*Int[Gamma[n-1,a+b*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x] && IGtQ[n,1]


Int[(c_.+d_.*x_)^m_.*Gamma[n_,a_.+b_.*x_],x_Symbol] :=
  Block[{$UseGamma=True},
    (c+d*x)^(m+1)*Gamma[n,a+b*x]/(d*(m+1)) + 
    b/(d*(m+1))*Int[(c+d*x)^(m+1)*(a+b*x)^(n-1)/E^(a+b*x),x]] /;
FreeQ[{a,b,c,d,m,n},x] && (IGtQ[m,0] || IGtQ[n,0] || IntegersQ[m,n]) && NeQ[m,-1]


Int[(c_.+d_.*x_)^m_.*Gamma[n_,a_.+b_.*x_],x_Symbol] :=
  Unintegrable[(c+d*x)^m*Gamma[n,a+b*x],x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[LogGamma[a_.+b_.*x_],x_Symbol] :=
  PolyGamma[-2,a+b*x]/b /;
FreeQ[{a,b},x]


Int[(c_.+d_.*x_)^m_.*LogGamma[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*PolyGamma[-2,a+b*x]/b -
  d*m/b*Int[(c+d*x)^(m-1)*PolyGamma[-2,a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*LogGamma[a_.+b_.*x_],x_Symbol] :=
  Unintegrable[(c+d*x)^m*LogGamma[a+b*x],x] /;
FreeQ[{a,b,c,d,m},x]


Int[PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
  PolyGamma[n-1,a+b*x]/b /;
FreeQ[{a,b,n},x]


Int[(c_.+d_.*x_)^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*PolyGamma[n-1,a+b*x]/b - d*m/b*Int[(c+d*x)^(m-1)*PolyGamma[n-1,a+b*x],x] /;
FreeQ[{a,b,c,d,n},x] && GtQ[m,0]


Int[(c_.+d_.*x_)^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*PolyGamma[n,a+b*x]/(d*(m+1)) -
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*PolyGamma[n+1,a+b*x],x] /;
FreeQ[{a,b,c,d,n},x] && LtQ[m,-1]


Int[(c_.+d_.*x_)^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
  Unintegrable[(c+d*x)^m*PolyGamma[n,a+b*x],x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[Gamma[a_.+b_.*x_]^n_.*PolyGamma[0,a_.+b_.*x_],x_Symbol] :=
  Gamma[a+b*x]^n/(b*n) /;
FreeQ[{a,b,n},x]


Int[((a_.+b_.*x_)!)^n_.*PolyGamma[0,c_.+b_.*x_],x_Symbol] :=
  ((a+b*x)!)^n/(b*n) /;
FreeQ[{a,b,c,n},x] && EqQ[c,a+1]


Int[Gamma[p_,d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  x*Gamma[p,d*(a+b*Log[c*x^n])] + b*d*n*E^(-a*d)*Int[(d*(a+b*Log[c*x^n]))^(p-1)/(c*x^n)^(b*d),x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[Gamma[p_,d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
  1/n*Subst[Gamma[p,d*(a+b*x)],x,Log[c*x^n]] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(e_.*x_)^m_.*Gamma[p_,d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  (e*x)^(m+1)*Gamma[p,d*(a+b*Log[c*x^n])]/(e*(m+1)) + 
  b*d*n*E^(-a*d)*(e*x)^(b*d*n)/((m+1)*(c*x^n)^(b*d))*Int[(e*x)^(m-b*d*n)*(d*(a+b*Log[c*x^n]))^(p-1),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[m,-1]


Int[Gamma[p_,f_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])],x_Symbol] :=
  1/e*Subst[Int[Gamma[p,f*(a+b*Log[c*x^n])],x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,n,p},x]


Int[(g_+h_. x_)^m_.*Gamma[p_,f_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])],x_Symbol] :=
  1/e*Subst[Int[(g*x/d)^m*Gamma[p,f*(a+b*Log[c*x^n])],x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[e*g-d*h,0]





(* ::Subsection::Closed:: *)
(*8.7 Zeta function*)


Int[Zeta[2,a_.+b_.*x_],x_Symbol] :=
  Int[PolyGamma[1,a+b*x],x] /;
FreeQ[{a,b},x]


Int[Zeta[s_,a_.+b_.*x_],x_Symbol] :=
  -Zeta[s-1,a+b*x]/(b*(s-1)) /;
FreeQ[{a,b,s},x] && NeQ[s,1] && NeQ[s,2]


Int[(c_.+d_.*x_)^m_.*Zeta[2,a_.+b_.*x_],x_Symbol] :=
  Int[(c+d*x)^m*PolyGamma[1,a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m]


Int[(c_.+d_.*x_)^m_.*Zeta[s_,a_.+b_.*x_],x_Symbol] :=
  -(c+d*x)^m*Zeta[s-1,a+b*x]/(b*(s-1)) +
  d*m/(b*(s-1))*Int[(c+d*x)^(m-1)*Zeta[s-1,a+b*x],x] /;
FreeQ[{a,b,c,d,s},x] && NeQ[s,1] && NeQ[s,2] && GtQ[m,0]


Int[(c_.+d_.*x_)^m_.*Zeta[s_,a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Zeta[s,a+b*x]/(d*(m+1)) +
  b*s/(d*(m+1))*Int[(c+d*x)^(m+1)*Zeta[s+1,a+b*x],x] /;
FreeQ[{a,b,c,d,s},x] && NeQ[s,1] && NeQ[s,2] && LtQ[m,-1]





(* ::Subsection::Closed:: *)
(*8.8 Polylogarithm function*)


Int[PolyLog[2,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  x*PolyLog[2,a*(b*x^p)^q] + p*q*Int[Log[1-a*(b*x^p)^q],x] /;
FreeQ[{a,b,p,q},x]


Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  x*PolyLog[n,a*(b*x^p)^q] - p*q*Int[PolyLog[n-1,a*(b*x^p)^q],x] /;
FreeQ[{a,b,p,q},x] && GtQ[n,0]


Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  x*PolyLog[n+1,a*(b*x^p)^q]/(p*q) - 1/(p*q)*Int[PolyLog[n+1,a*(b*x^p)^q],x] /;
FreeQ[{a,b,p,q},x] && LtQ[n,-1]


Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  Unintegrable[PolyLog[n,a*(b*x^p)^q],x] /;
FreeQ[{a,b,n,p,q},x]


Int[PolyLog[n_,c_.*(a_.+b_.*x_)^p_.]/(d_.+e_.*x_),x_Symbol] :=
  PolyLog[n+1,c*(a+b*x)^p]/(e*p) /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d,a*e]


Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.]/x_,x_Symbol] :=
  PolyLog[n+1,a*(b*x^p)^q]/(p*q) /;
FreeQ[{a,b,n,p,q},x]


Int[(d_.*x_)^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  (d*x)^(m+1)*PolyLog[n,a*(b*x^p)^q]/(d*(m+1)) - 
  p*q/(m+1)*Int[(d*x)^m*PolyLog[n-1,a*(b*x^p)^q],x] /;
FreeQ[{a,b,d,m,p,q},x] && NeQ[m,-1] && GtQ[n,0]


Int[(d_.*x_)^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  (d*x)^(m+1)*PolyLog[n+1,a*(b*x^p)^q]/(d*p*q) - 
  (m+1)/(p*q)*Int[(d*x)^m*PolyLog[n+1,a*(b*x^p)^q],x] /;
FreeQ[{a,b,d,m,p,q},x] && NeQ[m,-1] && LtQ[n,-1]


Int[(d_.*x_)^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  Unintegrable[(d*x)^m*PolyLog[n,a*(b*x^p)^q],x] /;
FreeQ[{a,b,d,m,n,p,q},x]


Int[Log[c_.*x_^m_.]^r_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.]/x_,x_Symbol] :=
  Log[c*x^m]^r*PolyLog[n+1,a*(b*x^p)^q]/(p*q) - 
  m*r/(p*q)*Int[Log[c*x^m]^(r-1)*PolyLog[n+1,a*(b*x^p)^q]/x,x] /;
FreeQ[{a,b,c,m,n,q,r},x] && GtQ[r,0]


Int[PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
  x*PolyLog[n,c*(a+b*x)^p] -
  p*Int[PolyLog[n-1,c*(a+b*x)^p],x] +
  a*p*Int[PolyLog[n-1,c*(a+b*x)^p]/(a+b*x),x] /;
FreeQ[{a,b,c,p},x] && GtQ[n,0]


Int[PolyLog[2,c_.*(a_.+b_.*x_)]/(d_.+e_.*x_),x_Symbol] :=
  Log[d+e*x]*PolyLog[2,c*(a+b*x)]/e + b/e*Int[Log[d+e*x]*Log[1-a*c-b*c*x]/(a+b*x),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)^m_.*PolyLog[2,c_.*(a_.+b_.*x_)],x_Symbol] :=
  (d+e*x)^(m+1)*PolyLog[2,c*(a+b*x)]/(e*(m+1)) + b/(e*(m+1))*Int[(d+e*x)^(m+1)*Log[1-a*c-b*c*x]/(a+b*x),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]


(* Int[(d_.+e_.*x_)^m_.*PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
  (d+e*x)^(m+1)*PolyLog[n,c*(a+b*x)^p]/(e*(m+1)) -
  b*p/(e*(m+1))*Int[(d+e*x)^(m+1)*PolyLog[n-1,c*(a+b*x)^p]/(a+b*x),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && GtQ[n,0] && IGtQ[m,0] *)


Int[x_^m_.*PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
  -(a^(m+1)-b^(m+1)*x^(m+1))*PolyLog[n,c*(a+b*x)^p]/((m+1)*b^(m+1)) +
  p/((m+1)*b^m)*Int[ExpandIntegrand[PolyLog[n-1,c*(a+b*x)^p],(a^(m+1)-b^(m+1)*x^(m+1))/(a+b*x),x],x] /;
FreeQ[{a,b,c,p},x] && GtQ[n,0] && IntegerQ[m] && NeQ[m,-1]


Int[PolyLog[n_,d_.*(F_^(c_.*(a_.+b_.*x_)))^p_.],x_Symbol] :=
  PolyLog[n+1,d*(F^(c*(a+b*x)))^p]/(b*c*p*Log[F]) /;
FreeQ[{F,a,b,c,d,n,p},x]


Int[(e_.+f_.*x_)^m_.*PolyLog[n_,d_.*(F_^(c_.*(a_.+b_.*x_)))^p_.],x_Symbol] :=
  (e+f*x)^m*PolyLog[n+1,d*(F^(c*(a+b*x)))^p]/(b*c*p*Log[F]) - 
  f*m/(b*c*p*Log[F])*Int[(e+f*x)^(m-1)*PolyLog[n+1,d*(F^(c*(a+b*x)))^p],x] /;
FreeQ[{F,a,b,c,d,e,f,n,p},x] && GtQ[m,0]


Int[u_*PolyLog[n_,v_],x_Symbol] :=
  With[{w=DerivativeDivides[v,u*v,x]},
  w*PolyLog[n+1,v] /;
 Not[FalseQ[w]]] /;
FreeQ[n,x]


Int[u_*Log[w_]*PolyLog[n_,v_],x_Symbol] :=
  With[{z=DerivativeDivides[v,u*v,x]},
  z*Log[w]*PolyLog[n+1,v] - 
  Int[SimplifyIntegrand[z*D[w,x]*PolyLog[n+1,v]/w,x],x] /;
 Not[FalseQ[z]]] /;
FreeQ[n,x] && InverseFunctionFreeQ[w,x]





(* ::Subsection::Closed:: *)
(*8.9 Product logarithm function*)


Int[(c_.*ProductLog[a_.+b_.*x_])^p_,x_Symbol] :=
  (a+b*x)*(c*ProductLog[a+b*x])^p/(b*(p+1)) +
  p/(c*(p+1))*Int[(c*ProductLog[a+b*x])^(p+1)/(1+ProductLog[a+b*x]),x] /;
FreeQ[{a,b,c},x] && LtQ[p,-1]


Int[(c_.*ProductLog[a_.+b_.*x_])^p_.,x_Symbol] :=
  (a+b*x)*(c*ProductLog[a+b*x])^p/b -
  p*Int[(c*ProductLog[a+b*x])^p/(1+ProductLog[a+b*x]),x] /;
FreeQ[{a,b,c},x] && Not[LtQ[p,-1]]


Int[(e_.+f_.*x_)^m_.*(c_.*ProductLog[a_+b_.*x_])^p_.,x_Symbol] :=
  1/b^(m+1)*Subst[Int[ExpandIntegrand[(c*ProductLog[x])^p,(b*e-a*f+f*x)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,e,f,p},x] && IGtQ[m,0]


Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
  x*(c*ProductLog[a*x^n])^p -
  n*p*Int[(c*ProductLog[a*x^n])^p/(1+ProductLog[a*x^n]),x] /;
FreeQ[{a,c,n,p},x] && (EqQ[n*(p-1),-1] || IntegerQ[p-1/2] && EqQ[n*(p-1/2),-1])


Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
  x*(c*ProductLog[a*x^n])^p/(n*p+1) +
  n*p/(c*(n*p+1))*Int[(c*ProductLog[a*x^n])^(p+1)/(1+ProductLog[a*x^n]),x] /;
FreeQ[{a,c,n},x] && (IntegerQ[p] && EqQ[n*(p+1),-1] || IntegerQ[p-1/2] && EqQ[n*(p+1/2),-1])


Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(c*ProductLog[a*x^(-n)])^p/x^2,x],x,1/x] /;
FreeQ[{a,c,p},x] && ILtQ[n,0]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_.,x_Symbol] :=
  x^(m+1)*(c*ProductLog[a*x^n])^p/(m+1) -
  n*p/(m+1)*Int[x^m*(c*ProductLog[a*x^n])^p/(1+ProductLog[a*x^n]),x] /;
FreeQ[{a,c,m,n,p},x] && NeQ[m,-1] &&
(IntegerQ[p-1/2] && IGtQ[2*Simplify[p+(m+1)/n],0] || Not[IntegerQ[p-1/2]] && IGtQ[Simplify[p+(m+1)/n]+1,0])


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_.,x_Symbol] :=
  x^(m+1)*(c*ProductLog[a*x^n])^p/(m+n*p+1) +
  n*p/(c*(m+n*p+1))*Int[x^m*(c*ProductLog[a*x^n])^(p+1)/(1+ProductLog[a*x^n]),x] /;
FreeQ[{a,c,m,n,p},x] &&
(EqQ[m,-1] || IntegerQ[p-1/2] && ILtQ[Simplify[p+(m+1)/n]-1/2,0] || Not[IntegerQ[p-1/2]] && ILtQ[Simplify[p+(m+1)/n],0])


Int[x_^m_.*(c_.*ProductLog[a_.*x_])^p_.,x_Symbol] :=
  Int[x^m*(c*ProductLog[a*x])^p/(1+ProductLog[a*x]),x] +
  1/c*Int[x^m*(c*ProductLog[a*x])^(p+1)/(1+ProductLog[a*x]),x] /;
FreeQ[{a,c,m},x]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(c*ProductLog[a*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,p},x] && ILtQ[n,0] && IntegerQ[m] && NeQ[m,-1]


Int[1/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  (a+b*x)/(b*d*ProductLog[a+b*x]) /;
FreeQ[{a,b,d},x]


Int[ProductLog[a_.+b_.*x_]/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  d*x - Int[1/(d+d*ProductLog[a+b*x]),x] /;
FreeQ[{a,b,d},x]


Int[(c_.*ProductLog[a_.+b_.*x_])^p_/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  c*(a+b*x)*(c*ProductLog[a+b*x])^(p-1)/(b*d) -
  c*p*Int[(c*ProductLog[a+b*x])^(p-1)/(d+d*ProductLog[a+b*x]),x] /;
FreeQ[{a,b,c,d},x] && GtQ[p,0]


Int[1/(ProductLog[a_.+b_.*x_]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
  ExpIntegralEi[ProductLog[a+b*x]]/(b*d) /;
FreeQ[{a,b,d},x]


Int[1/(Sqrt[c_.*ProductLog[a_.+b_.*x_]]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
  Rt[Pi*c,2]*Erfi[Sqrt[c*ProductLog[a+b*x]]/Rt[c,2]]/(b*c*d) /;
FreeQ[{a,b,c,d},x] && PosQ[c]


Int[1/(Sqrt[c_.*ProductLog[a_.+b_.*x_]]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
  Rt[-Pi*c,2]*Erf[Sqrt[c*ProductLog[a+b*x]]/Rt[-c,2]]/(b*c*d) /;
FreeQ[{a,b,c,d},x] && NegQ[c]


Int[(c_.*ProductLog[a_.+b_.*x_])^p_/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  (a+b*x)*(c*ProductLog[a+b*x])^p/(b*d*(p+1)) -
  1/(c*(p+1))*Int[(c*ProductLog[a+b*x])^(p+1)/(d+d*ProductLog[a+b*x]),x] /;
FreeQ[{a,b,c,d},x] && LtQ[p,-1]


Int[(c_.*ProductLog[a_.+b_.*x_])^p_./(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  Gamma[p+1,-ProductLog[a+b*x]]*(c*ProductLog[a+b*x])^p/(b*d*(-ProductLog[a+b*x])^p) /;
FreeQ[{a,b,c,d,p},x]


Int[(e_.+f_.*x_)^m_./(d_+d_.*ProductLog[a_+b_.*x_]),x_Symbol] :=
  1/b^(m+1)*Subst[Int[ExpandIntegrand[1/(d+d*ProductLog[x]),(b*e-a*f+f*x)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,d,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*(c_.*ProductLog[a_+b_.*x_])^p_./(d_+d_.*ProductLog[a_+b_.*x_]),x_Symbol] :=
  1/b^(m+1)*Subst[Int[ExpandIntegrand[(c*ProductLog[x])^p/(d+d*ProductLog[x]),(b*e-a*f+f*x)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,d,e,f,p},x] && IGtQ[m,0]


Int[1/(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
  -Subst[Int[1/(x^2*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
FreeQ[{a,d},x] && ILtQ[n,0]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  c*x*(c*ProductLog[a*x^n])^(p-1)/d /;
FreeQ[{a,c,d,n,p},x] && EqQ[n*(p-1),-1]


Int[ProductLog[a_.*x_^n_.]^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  a^p*ExpIntegralEi[-p*ProductLog[a*x^n]]/(d*n) /;
FreeQ[{a,d},x] && IntegerQ[p] && EqQ[n*p,-1]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  Rt[Pi*c*n,2]/(d*n*a^(1/n)*c^(1/n))*Erfi[Sqrt[c*ProductLog[a*x^n]]/Rt[c*n,2]] /;
FreeQ[{a,c,d},x] && IntegerQ[1/n] && EqQ[p,1/2-1/n] && PosQ[c*n]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  Rt[-Pi*c*n,2]/(d*n*a^(1/n)*c^(1/n))*Erf[Sqrt[c*ProductLog[a*x^n]]/Rt[-c*n,2]] /;
FreeQ[{a,c,d},x] && IntegerQ[1/n] && EqQ[p,1/2-1/n] && NegQ[c*n]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  c*x*(c*ProductLog[a*x^n])^(p-1)/d -
  c*(n*(p-1)+1)*Int[(c*ProductLog[a*x^n])^(p-1)/(d+d*ProductLog[a*x^n]),x] /;
FreeQ[{a,c,d},x] && GtQ[n,0] && GtQ[n*(p-1)+1,0]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  x*(c*ProductLog[a*x^n])^p/(d*(n*p+1)) -
  1/(c*(n*p+1))*Int[(c*ProductLog[a*x^n])^(p+1)/(d+d*ProductLog[a*x^n]),x] /;
FreeQ[{a,c,d},x] && GtQ[n,0] && LtQ[n*p+1,0]


Int[(c_.*ProductLog[a_.*x_^n_])^p_./(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
  -Subst[Int[(c*ProductLog[a*x^(-n)])^p/(x^2*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
FreeQ[{a,c,d,p},x] && ILtQ[n,0]


Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
  x^(m+1)/(d*(m+1)*ProductLog[a*x]) -
  m/(m+1)*Int[x^m/(ProductLog[a*x]*(d+d*ProductLog[a*x])),x] /;
FreeQ[{a,d},x] && GtQ[m,0]


Int[1/(x_*(d_+d_.*ProductLog[a_.*x_])),x_Symbol] :=
  Log[ProductLog[a*x]]/d /;
FreeQ[{a,d},x]


Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
  x^(m+1)/(d*(m+1)) -
  Int[x^m*ProductLog[a*x]/(d+d*ProductLog[a*x]),x] /;
FreeQ[{a,d},x] && LtQ[m,-1]


Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
  x^m*Gamma[m+1,-(m+1)*ProductLog[a*x]]/
	(a*d*(m+1)*E^(m*ProductLog[a*x])*(-(m+1)*ProductLog[a*x])^m) /;
FreeQ[{a,d,m},x] && Not[IntegerQ[m]]


Int[1/(x_*(d_+d_.*ProductLog[a_.*x_^n_.])),x_Symbol] :=
  Log[ProductLog[a*x^n]]/(d*n) /;
FreeQ[{a,d,n},x]


Int[x_^m_./(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
  -Subst[Int[1/(x^(m+2)*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
FreeQ[{a,d},x] && IntegerQ[m] && ILtQ[n,0] && NeQ[m,-1]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(x_*(d_+d_.*ProductLog[a_.*x_^n_.])),x_Symbol] :=
  (c*ProductLog[a*x^n])^p/(d*n*p) /;
FreeQ[{a,c,d,n,p},x]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  c*x^(m+1)*(c*ProductLog[a*x^n])^(p-1)/(d*(m+1)) /;
FreeQ[{a,c,d,m,n,p},x] && NeQ[m,-1] && EqQ[m+n*(p-1),-1]


Int[x_^m_.*ProductLog[a_.*x_^n_.]^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  a^p*ExpIntegralEi[-p*ProductLog[a*x^n]]/(d*n) /;
FreeQ[{a,d,m,n},x] && IntegerQ[p] && EqQ[m+n*p,-1]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  a^(p-1/2)*c^(p-1/2)*Rt[Pi*c/(p-1/2),2]*Erf[Sqrt[c*ProductLog[a*x^n]]/Rt[c/(p-1/2),2]]/(d*n) /;
FreeQ[{a,c,d,m,n},x] && NeQ[m,-1] && IntegerQ[p-1/2] && EqQ[m+n*(p-1/2),-1] && PosQ[c/(p-1/2)]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  a^(p-1/2)*c^(p-1/2)*Rt[-Pi*c/(p-1/2),2]*Erfi[Sqrt[c*ProductLog[a*x^n]]/Rt[-c/(p-1/2),2]]/(d*n) /;
FreeQ[{a,c,d,m,n},x] && NeQ[m,-1] && IntegerQ[p-1/2] && EqQ[m+n*(p-1/2),-1] && NegQ[c/(p-1/2)]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  c*x^(m+1)*(c*ProductLog[a*x^n])^(p-1)/(d*(m+1)) -
  c*(m+n*(p-1)+1)/(m+1)*Int[x^m*(c*ProductLog[a*x^n])^(p-1)/(d+d*ProductLog[a*x^n]),x] /;
FreeQ[{a,c,d,m,n,p},x] && NeQ[m,-1] && GtQ[Simplify[p+(m+1)/n],1]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  x^(m+1)*(c*ProductLog[a*x^n])^p/(d*(m+n*p+1)) -
  (m+1)/(c*(m+n*p+1))*Int[x^m*(c*ProductLog[a*x^n])^(p+1)/(d+d*ProductLog[a*x^n]),x] /;
FreeQ[{a,c,d,m,n,p},x] && NeQ[m,-1] && LtQ[Simplify[p+(m+1)/n],0]


Int[x_^m_.*(c_.*ProductLog[a_.*x_])^p_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
  x^m*Gamma[m+p+1,-(m+1)*ProductLog[a*x]]*(c*ProductLog[a*x])^p/
	(a*d*(m+1)*E^(m*ProductLog[a*x])*(-(m+1)*ProductLog[a*x])^(m+p)) /;
FreeQ[{a,c,d,m,p},x] && NeQ[m,-1]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  -Subst[Int[(c*ProductLog[a*x^(-n)])^p/(x^(m+2)*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
FreeQ[{a,c,d,p},x] && NeQ[m,-1] && IntegerQ[m] && LtQ[n,0]


Int[u_,x_Symbol] :=
  Subst[Int[SimplifyIntegrand[(x+1)*E^x*SubstFor[ProductLog[x],u,x],x],x],x,ProductLog[x]] /;
FunctionOfQ[ProductLog[x],u,x]



