(* ::Package:: *)

(************************************************************************)
(* This file was generated automatically by the Mathematica front end.  *)
(* It contains Initialization cells from a Notebook file, which         *)
(* typically will have the same name as this file except ending in      *)
(* ".nb" instead of ".m".                                               *)
(*                                                                      *)
(* This file is intended to be loaded into the Mathematica kernel using *)
(* the package loading commands Get or Needs.  Doing so is equivalent   *)
(* to using the Evaluate Initialization Cells menu command in the front *)
(* end.                                                                 *)
(*                                                                      *)
(* DO NOT EDIT THIS FILE.  This entire file is regenerated              *)
(* automatically each time the parent Notebook file is saved in the     *)
(* Mathematica front end.  Any changes you make to this file will be    *)
(* overwritten.                                                         *)
(************************************************************************)



(* ::Code:: *)
(* Int[u_.*(v_+w_)^p_.,x_Symbol] :=
  Int[u*w^p,x] /;
FreeQ[p,x] && ZeroQ[v] *)


(* ::Code:: *)
Int[u_.*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[u*(b*x^n)^p,x] /;
FreeQ[{a,b,n,p},x] && ZeroQ[a]


(* ::Code:: *)
Int[u_.*(a_.+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[u*a^p,x] /;
FreeQ[{a,b,n,p},x] && ZeroQ[b]


(* ::Code:: *)
Int[u_.*(a_+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[u*(b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j-2*n] && ZeroQ[a]


(* ::Code:: *)
Int[u_.*(a_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[u*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b]


(* ::Code:: *)
Int[u_.*(a_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[u*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j-2*n] && ZeroQ[c]


(* ::Code:: *)
Int[u_.*v_^m_,x_Symbol] :=
  Int[u*v^Simplify[m],x] /;
PolynomialQ[v,x] && Not[RationalQ[m]] && FreeQ[m,x] && RationalQ[Simplify[m]]


(* ::Code:: *)
Int[a_,x_Symbol] :=
   a*x /;
FreeQ[a,x]


(* ::Code:: *)
Int[a_*(b_+c_.*x_),x_Symbol] :=
  a*(b+c*x)^2/(2*c) /;
FreeQ[{a,b,c},x]


(* ::Code:: *)
Int[-u_,x_Symbol] :=
  Identity[-1]*Int[u,x]


(* ::Code:: *)
Int[Complex[0,a_]*u_,x_Symbol] :=
  Complex[Identity[0],a]*Int[u,x] /;
FreeQ[a,x] && OneQ[a^2]


(* ::Code:: *)
Int[a_*u_,x_Symbol] :=
  a*Int[u,x] /;
FreeQ[a,x] && Not[MatchQ[u, b_*v_ /; FreeQ[b,x]]]


(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
  ShowStep["","Int[a*u + b*v + \[CenterEllipsis],x]","a*Integrate[u,x] + b*Integrate[v,x] + \[CenterEllipsis]",Hold[
  IntSum[u,x]]] /;
SimplifyFlag && SumQ[u],

Int[u_,x_Symbol] :=
  IntSum[u,x] /;
SumQ[u]]


(* ::Code:: *)
Int[(c_.*x_)^m_.*u_,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*u,x],x] /;
FreeQ[{c,m},x] && SumQ[u] && Not[MatchQ[u,a_+b_.*v_ /; FreeQ[{a,b},x] && InverseFunctionQ[v]]]


(* ::Code:: *)
(* Int[u_.*(c_.*x_^n_)^p_,x_Symbol] :=
  c^(p-1/2)*Sqrt[c*x^n]/x^(n/2)*Int[u*x^(n*p),x] /;
FreeQ[{c,n,p},x] && PositiveIntegerQ[p+1/2] *)


(* ::Code:: *)
(* Int[u_.*(c_.*x_^n_)^p_,x_Symbol] :=
  c^(p+1/2)*x^(n/2)/Sqrt[c*x^n]*Int[u*x^(n*p),x] /;
FreeQ[{c,n,p},x] && NegativeIntegerQ[p-1/2] *)


(* ::Code:: *)
(* Int[u_.*(c_.*x_^n_)^p_,x_Symbol] :=
  (c*x^n)^p/(x^(n*p))*Int[u*x^(n*p),x] /;
FreeQ[{c,n,p},x] && Not[IntegerQ[2*p]] *)


(* ::Code:: *)
Int[u_.*(c_.*(a_.+b_.* x_)^n_)^p_,x_Symbol] :=
  c^(p-1/2)*Sqrt[c*(a+b*x)^n]/(a+b*x)^(n/2)*Int[u*(a+b*x)^(n*p),x] /;
FreeQ[{a,b,c,n,p},x] && PositiveIntegerQ[p+1/2]


(* ::Code:: *)
Int[u_.*(c_.*(a_.+b_.* x_)^n_)^p_,x_Symbol] :=
  c^(p+1/2)*(a+b*x)^(n/2)/Sqrt[c*(a+b*x)^n]*Int[u*(a+b*x)^(n*p),x] /;
FreeQ[{a,b,c,n,p},x] && NegativeIntegerQ[p-1/2]


(* ::Code:: *)
Int[u_.*(c_.*(a_.+b_.* x_)^n_)^p_,x_Symbol] :=
  (c*(a+b*x)^n)^p/((a+b*x)^(n*p))*Int[u*(a+b*x)^(n*p),x] /;
FreeQ[{a,b,c,n,p},x] && Not[IntegerQ[2*p]]


(* ::Code:: *)
Int[u_.*(c_.*(d_*(a_.+b_.* x_))^p_)^q_,x_Symbol] :=
  (c*(d*(a+b*x))^p)^q/(a+b*x)^(p*q)*Int[u*(a+b*x)^(p*q),x] /;
FreeQ[{a,b,c,d,p,q},x] && Not[IntegerQ[p]] && Not[IntegerQ[q]]


(* ::Code:: *)
Int[u_.*(c_.*(d_.*(a_.+b_.* x_)^n_)^p_)^q_,x_Symbol] :=
  (c*(d*(a+b*x)^n)^p)^q/(a+b*x)^(n*p*q)*Int[u*(a+b*x)^(n*p*q),x] /;
FreeQ[{a,b,c,d,n,p,q},x] && Not[IntegerQ[p]] && Not[IntegerQ[q]]


(* ::Code:: *)
Int[u_.*v_^m_.*(b_*v_)^n_,x_Symbol] :=
  1/b^m*Int[u*(b*v)^(m+n),x] /;
FreeQ[{b,n},x] && IntegerQ[m]


(* ::Code:: *)
Int[u_.*(a_.*v_)^m_*(b_.*v_)^n_,x_Symbol] :=
  a^(m+1/2)*b^(n-1/2)*Sqrt[b*v]/Sqrt[a*v]*Int[u*v^(m+n),x] /;
FreeQ[{a,b,m},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2] && IntegerQ[m+n]


(* ::Code:: *)
(* Int[u_.*(a_.*v_)^m_*(b_.*v_)^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*v]/(a^(n-1/2)*Sqrt[a*v])*Int[u*(a*v)^(m+n),x] /;
FreeQ[{a,b,m},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2] && Not[IntegerQ[m+n]] *)


(* ::Code:: *)
Int[u_.*(a_.*v_)^m_*(b_.*v_)^n_,x_Symbol] :=
  a^(m-1/2)*b^(n+1/2)*Sqrt[a*v]/Sqrt[b*v]*Int[u*v^(m+n),x] /;
FreeQ[{a,b,m},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2] && IntegerQ[m+n]


(* ::Code:: *)
(* Int[u_.*(a_.*v_)^m_*(b_.*v_)^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[a*v]/(a^(n+1/2)*Sqrt[b*v])*Int[u*(a*v)^(m+n),x] /;
FreeQ[{a,b,m},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2] && Not[IntegerQ[m+n]] *)


(* ::Code:: *)
Int[u_.*(a_.*v_)^m_*(b_.*v_)^n_,x_Symbol] :=
  a^(m+n)*(b*v)^n/(a*v)^n*Int[u*v^(m+n),x] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && IntegerQ[m+n]


(* ::Code:: *)
Int[u_.*(a_.*v_)^m_*(b_.*v_)^n_,x_Symbol] :=
  (b*v)^n/(a*v)^n*Int[u*(a*v)^(m+n),x] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[m+n]]


(* ::Code:: *)
Int[u_.*(a_+b_.*v_)^m_.*(c_+d_.*v_)^n_.,x_Symbol] :=
  (b/d)^m*Int[u*(c+d*v)^(m+n),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[b*c-a*d] && (IntegerQ[m] || PositiveQ[b/d]) && (Not[IntegerQ[n]] || LeafCount[c+d*x]<=LeafCount[a+b*x])


(* ::Code:: *)
Int[u_.*(a_+b_.*v_)^m_*(c_+d_.*v_)^n_,x_Symbol] :=
  (a+b*v)^m/(c+d*v)^m*Int[u*(c+d*v)^(m+n),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[b*c-a*d] && Not[IntegerQ[m] || IntegerQ[n] || PositiveQ[b/d]]


(* ::Code:: *)
Int[u_.*(a_+b_.*v_)^m_.*(c_+d_.*v_)^n_.,x_Symbol] :=
  (b/d)^m*Int[u*(c+d*v)^(m+n),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[b*c-a*d] && (IntegerQ[m] || PositiveQ[b/d]) && (Not[IntegerQ[n]] || LeafCount[c+d*x]<=LeafCount[a+b*x])


(* ::Code:: *)
Int[u_.*(a_+b_.*v_)^m_*(c_+d_.*v_)^n_,x_Symbol] :=
  (a+b*v)^m/(c+d*v)^m*Int[u*(c+d*v)^(m+n),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[b*c-a*d] && Not[IntegerQ[m] || IntegerQ[n] || PositiveQ[b/d]]


(* ::Code:: *)
Int[u_.*(a_.*v_)^m_*(b_.*v_+c_.*v_^2),x_Symbol] :=
  1/a*Int[u*(a*v)^(m+1)*Simp[b+c*v,x],x] /;
FreeQ[{a,b,c},x] && RationalQ[m] && m<=-1


(* ::Code:: *)
Int[u_.*(a_+b_.*v_)^m_*(A_.+B_.*v_+C_.*v_^2),x_Symbol] :=
  1/b^2*Int[u*(a+b*v)^(m+1)*Simp[b*B-a*C+b*C*v,x],x] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[m] && m<=-1


(* ::Code:: *)
Int[u_.*(a_+b_.*x_^n_.)^m_.*(c_+d_.*x_^q_.)^p_.,x_Symbol] :=
  (d/a)^p*Int[u*(a+b*x^n)^(m+p)/x^(n*p),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[n+q] && IntegerQ[p] && ZeroQ[a*c-b*d] && Not[IntegerQ[m] && NegQ[n]]


(* ::Code:: *)
Int[u_.*(a_+b_.*x_^n_.)^m_.*(c_+d_.*x_^j_)^p_.,x_Symbol] :=
  (-b^2/d)^m*Int[u*(a-b*x^n)^(-m),x] /;
FreeQ[{a,b,c,d,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[m+p] && ZeroQ[b^2*c+a^2*d] && PositiveQ[a] && NegativeQ[d]


(* ::Code:: *)
Int[u_.*(a_.*x_^r_.+b_.*x_^s_.)^m_.,x_Symbol] :=
  Int[u*x^(m*r)*(a+b*x^(s-r))^m,x] /;
FreeQ[{a,b,m,r,s},x] && IntegerQ[m] && PosQ[s-r]



