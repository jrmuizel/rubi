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
Int[(c_+d_.*x_^2)/((e_+f_.*x_^2)*Sqrt[a_+b_.*x_^4]),x_Symbol] :=
  c/(e*Rt[2*b*c/d,2])*ArcTanh[Rt[2*b*c/d,2]*(x/Sqrt[a+b*x^4])] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[b*c^2-a*d^2] && ZeroQ[d*e+c*f] && PosQ[b*c/d]


(* ::Code:: *)
Int[(c_+d_.*x_^2)/((e_+f_.*x_^2)*Sqrt[a_+b_.*x_^4]),x_Symbol] :=
  c/(e*Rt[-2*b*c/d,2])*ArcTan[Rt[-2*b*c/d,2]*(x/Sqrt[a+b*x^4])] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[b*c^2-a*d^2] && ZeroQ[d*e+c*f] && NegQ[b*c/d]


(* ::Code:: *)
Int[Sqrt[a_.*x_+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
  2/(3*a)*(2*a*x-b*Sqrt[c+a^2*x^2/b^2])*Sqrt[a*x+b*Sqrt[c+a^2*x^2/b^2]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[d-a^2/b^2]


(* ::Code:: *)
Int[Sqrt[a_+b_.*Sqrt[d_+c_.*x_^2]],x_Symbol] :=
  2/(3*c*x)*(-a^2/b^2+c*x^2+a/b*Sqrt[a^2/b^2+c*x^2])*Sqrt[a+b*Sqrt[a^2/b^2+c*x^2]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[d-a^2/b^2]


(* ::Code:: *)
Int[Sqrt[b_.*x_^2+Sqrt[a_+c_.*x_^4]]/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  ArcTanh[Rt[2*b,2]*x/Sqrt[b*x^2+Sqrt[a+c*x^4]]]/Rt[2*b,2] /;
FreeQ[{a,b,c},x] && ZeroQ[c-b^2] && PosQ[b]


(* ::Code:: *)
Int[Sqrt[b_.*x_^2+Sqrt[a_+c_.*x_^4]]/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  ArcTan[Rt[-2*b,2]*x/Sqrt[b*x^2+Sqrt[a+c*x^4]]]/Rt[-2*b,2] /;
FreeQ[{a,b,c},x] && ZeroQ[c-b^2] && NegQ[b]


(* ::Code:: *)
Int[(c_.+d_.*x_)^m_.*Sqrt[b_.*x_^2+Sqrt[a_+e_.*x_^4]]/Sqrt[a_+e_.*x_^4],x_Symbol] :=
  (1-I)/2*Int[(c+d*x)^m/Sqrt[Sqrt[a]-I*b*x^2],x] +
  (1+I)/2*Int[(c+d*x)^m/Sqrt[Sqrt[a]+I*b*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[e-b^2] && PositiveQ[a]


(* ::Code:: *)
Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*a^(2*p))*Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d},x] && IntegerQ[p] && ZeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+b*x+d*x^3)^p,x],x] /;
FreeQ[{a,b,d},x] && PositiveIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+d*x^3]},
  Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p))*Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && ZeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+d*x^3]},
  (a+b*x+d*x^3)^p/Map[Function[#^p],u]*Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  (a+b*x+d*x^3)^p/(((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p)*
    Int[((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*a^(2*p))*Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,e,f,m},x] && IntegerQ[p] && ZeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(e+f*x)^m,(a+b*x+d*x^3)^p,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+d*x^3]},
  Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p))*Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+d*x^3]},
  (a+b*x+d*x^3)^p/Map[Function[#^p],u]*Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  (a+b*x+d*x^3)^p/(((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p)*
    Int[(e+f*x)^m*((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


(* ::Code:: *)
Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  -1/(3^(3*p)*d^(2*p))*Int[(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d},x] && IntegerQ[p] && ZeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+c*x^2+d*x^3]},
  Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+c*x^2+d*x^3)^p/((c-3*d*x)^p*(2*c+3*d*x)^(2*p))*Int[(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+c*x^2+d*x^3]},
  (a+c*x^2+d*x^3)^p/Map[Function[#^p],u]*Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  (a+c*x^2+d*x^3)^p/((c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  -1/(3^(3*p)*d^(2*p))*Int[(e+f*x)^m*(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(e+f*x)^m,(a+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+c*x^2+d*x^3]},
  Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+c*x^2+d*x^3)^p/((c-3*d*x)^p*(2*c+3*d*x)^(2*p))*Int[(e+f*x)^m*(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+c*x^2+d*x^3]},
  (a+c*x^2+d*x^3)^p/Map[Function[#^p],u]*Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  (a+c*x^2+d*x^3)^p/((c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(e+f*x)^m*(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Int[(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Subst[Int[(3*a*b*c-b^3+c^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[b^3-3*a*b*c,3]},
  1/(3^p*b^p*c^p)*Int[(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[c^3-3*b*c*d,3]},
  1/(3^p*b^p*c^p)*Int[(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+b*x+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+c*x^2+d*x^3]},
  Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+c*x^2+d*x^3)^p/(b+c*x)^(3*p)*Int[(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[b^3-3*a*b*c,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p)*
    Int[(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[c^3-3*b*c*d,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p)*
    Int[(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+c*x^2+d*x^3]},
  (a+b*x+c*x^2+d*x^3)^p/Map[Function[#^p],u]*Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] *)


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  (a+b*x+c*x^2+d*x^3)^p/
    ((c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && PolyQ[u,x,3] && Not[CubicMatchQ[u,x]]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[b^3-3*a*b*c,3]},
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[c^3-3*b*c*d,3]},
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(e+f*x)^m,(a+b*x+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+c*x^2+d*x^3]},
  Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
(* Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+c*x^2+d*x^3)^p/(b+c*x)^(3*p)*Int[(e+f*x)^m*(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[b^3-3*a*b*c,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p)*
    Int[(e+f*x)^m*(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[c^3-3*b*c*d,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p)*
    Int[(e+f*x)^m*(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+c*x^2+d*x^3]},
  (a+b*x+c*x^2+d*x^3)^p/Map[Function[#^p],u]*Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
(* Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] *)


(* ::Code:: *)
Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  (a+b*x+c*x^2+d*x^3)^p/
    ((c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(e+f*x)^m*(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* ::Code:: *)
Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && LinearQ[u,x] && PolyQ[v,x,3] && Not[LinearMatchQ[u,x] && CubicMatchQ[v,x]]


(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  Subst[Int[SimplifyIntegrand[(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[d^3-4*c*d*e+8*b*e^2] && p=!=2 && p=!=3


(* ::Code:: *)
Int[v_^p_,x_Symbol] :=
  Module[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  Subst[Int[SimplifyIntegrand[(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
 ZeroQ[d^3-4*c*d*e+8*b*e^2] && NonzeroQ[d]] /;
FreeQ[p,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && p=!=2 && p=!=3


(* ::Code:: *)
Int[u_*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  Subst[Int[SimplifyIntegrand[ReplaceAll[u,x->-d/(4*e)+x]*(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
FreeQ[{a,b,c,d,e,p},x] && PolynomialQ[u,x] && ZeroQ[d^3-4*c*d*e+8*b*e^2] && Not[PositiveIntegerQ[p]]


(* ::Code:: *)
Int[u_*v_^p_,x_Symbol] :=
  Module[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  Subst[Int[SimplifyIntegrand[ReplaceAll[u,x->-d/(4*e)+x]*(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
 ZeroQ[d^3-4*c*d*e+8*b*e^2] && NonzeroQ[d]] /;
FreeQ[p,x] && PolynomialQ[u,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && Not[PositiveIntegerQ[p]]


(* ::Code:: *)
Int[(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  -16*a^2*Subst[
    Int[1/(b-4*a*x)^2*(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p,x],x,b/(4*a)+1/x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^3-4*a*b*c+8*a^2*d] && IntegerQ[2*p]


(* ::Code:: *)
Int[v_^p_,x_Symbol] :=
  Module[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  -16*a^2*Subst[
    Int[1/(b-4*a*x)^2*(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p,x],x,b/(4*a)+1/x] /;
 NonzeroQ[a] && NonzeroQ[b] && ZeroQ[b^3-4*a*b*c+8*a^2*d]] /;
FreeQ[p,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && IntegerQ[2*p]


(* ::Code:: *)
Int[(A_.+B_.*x_+C_.*x_^2+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[(b*A-2*a*B+2*a*D+A*q+(2*a*A-2*a*C+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[(b*A-2*a*B+2*a*D-A*q+(2*a*A-2*a*C+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,C,D},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


(* ::Code:: *)
Int[(A_.+B_.*x_+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[(b*A-2*a*B+2*a*D+A*q+(2*a*A+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[(b*A-2*a*B+2*a*D-A*q+(2*a*A+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,D},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


(* ::Code:: *)
Int[x_^m_.*(A_.+B_.*x_+C_.*x_^2+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[x^m*(b*A-2*a*B+2*a*D+A*q+(2*a*A-2*a*C+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[x^m*(b*A-2*a*B+2*a*D-A*q+(2*a*A-2*a*C+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,C,D,m},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


(* ::Code:: *)
Int[x_^m_.*(A_.+B_.*x_+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[x^m*(b*A-2*a*B+2*a*D+A*q+(2*a*A+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[x^m*(b*A-2*a*B+2*a*D-A*q+(2*a*A+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,D,m},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


(* ::Code:: *)
Int[(A_+B_.*x_^n_)/(a_+b_.*x_^2+c_.*x_^n_+d_.*x_^j_), x_Symbol] :=
  A/(a*Rt[b/a,2])*ArcTan[A*(n-1)*Rt[b/a,2]*x/(A*(n-1)-B*x^n)] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[j-2*n] && NonzeroQ[n-2] && 
  ZeroQ[a*B^2-A^2*d*(n-1)^2] && ZeroQ[B*c+2*A*d*(n-1)] && PosQ[b/a]


(* ::Code:: *)
Int[(A_+B_.*x_^n_)/(a_+b_.*x_^2+c_.*x_^n_+d_.*x_^j_), x_Symbol] :=
  A/(a*Rt[-b/a,2])*ArcTanh[A*(n-1)*Rt[-b/a,2]*x/(A*(n-1)-B*x^n)] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[j-2*n] && NonzeroQ[n-2] &&
  ZeroQ[B^2*a-A^2*d*(n-1)^2] && ZeroQ[B*c+2*A*d*(n-1)] && NegQ[b/a]


(* ::Code:: *)
Int[x_^m_.*(A_+B_.*x_^n_.)/(a_+b_.*x_^k_.+c_.*x_^n_.+d_.*x_^j_), x_Symbol] :=
  A/((m+1)*Rt[a*b,2])*ArcTan[A*(m-n+1)*Rt[a*b,2]*x^(m+1)/(a*(A*(m-n+1)+B*(m+1)*x^n))] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[j-2*n] && ZeroQ[k-2*(m+1)] &&
  ZeroQ[a*B^2*(m+1)^2-A^2*d*(m-n+1)^2] && ZeroQ[B*c*(m+1)-2*A*d*(m-n+1)] && PosQ[a*b]


(* ::Code:: *)
Int[x_^m_.*(A_+B_.*x_^n_.)/(a_+b_.*x_^k_.+c_.*x_^n_.+d_.*x_^j_), x_Symbol] :=
  A/((m+1)*Rt[-a*b,2])*ArcTanh[A*(m-n+1)*Rt[-a*b,2]*x^(m+1)/(a*(A*(m-n+1)+B*(m+1)*x^n))] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[j-2*n] && ZeroQ[k-2*(m+1)] &&
  ZeroQ[a*B^2*(m+1)^2-A^2*d*(m-n+1)^2] && ZeroQ[B*c*(m+1)-2*A*d*(m-n+1)] && NegQ[a*b]


(* ::Code:: *)
Int[u_^m_.*(a_.+b_.*(c_+d_.*x_)^n_)^p_,x_Symbol] :=
  Module[{k=Denominator[n]},
  k/d*Subst[Int[SimplifyIntegrand[x^(k-1)*ReplaceAll[u,x->x^k/d-c/d]^m*(a+b*x^(k*n))^p,x],x],x,(c+d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && PolynomialQ[u,x] && IntegerQ[m] && RationalQ[n]


(* ::Code:: *)
Int[u_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[PolynomialQuotient[u,a+b*x^n,x]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,p},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && ZeroQ[PolynomialRemainder[u,a+b*x^n,x]]


(* ::Code:: *)
Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Coefficient[u,x,n-1]*(a+b*x^n)^(p+1)/(b*n*(p+1)) + 
  Int[ExpandToSum[u-Coefficient[u,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n,p] && NonzeroQ[Coefficient[u,x,n-1]]


(* ::Code:: *)
Int[u_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[u*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n,p] && ZeroQ[Coefficient[u,x,n-1]]


(* ::Code:: *)
Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  B^3/b*Int[1/(A^2-A*B*x+B^2*x^2),x] /;
FreeQ[{a,b,A,B},x] && ZeroQ[a*B^3-b*A^3]


(* ::Code:: *)
Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  -r*(B*r-A*s)/(3*a*s)*Int[1/(r+s*x),x] + 
  r/(3*a*s)*Int[(r*(B*r+2*A*s)+s*(B*r-A*s)*x)/(r^2-r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b,A,B},x] && NonzeroQ[a*B^3-b*A^3] && PosQ[a/b]


(* ::Code:: *)
Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r*(B*r+A*s)/(3*a*s)*Int[1/(r-s*x),x] - 
  r/(3*a*s)*Int[(r*(B*r-2*A*s)-s*(B*r+A*s)*x)/(r^2+r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b,A,B},x] && NonzeroQ[a*B^3-b*A^3] && NegQ[a/b]


(* ::Code:: *)
Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Int[(A+B*x)/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,A,B,C},x] && (ZeroQ[a*B^3-b*A^3] || Not[RationalQ[a/b]])


(* ::Code:: *)
Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  B*Int[x/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,B,C},x] && Not[RationalQ[a/b]]


(* ::Code:: *)
Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  A*Int[1/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,A,C},x] && Not[RationalQ[a,b,A,C]]


(* ::Code:: *)
Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  q^2/a*Int[(A+C*q*x)/(q^2-q*x+x^2),x] /;
 ZeroQ[A-B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b>0


(* ::Code:: *)
Int[(B_*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  B*q^2/a*Int[x/(q^2-q*x+x^2),x] /;
 ZeroQ[-B+C*q]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b>0


(* ::Code:: *)
Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  q^2/a*Int[(A+C*q*x)/(q^2-q*x+x^2),x] /;
 ZeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b>0


(* ::Code:: *)
Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  q*(A-B*q+C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(2*A+B*q-C*q^2)-(A-B*q-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[A-B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b>0


(* ::Code:: *)
Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  -q*(B*q-C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(B*q-C*q^2)+(B*q+2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[B*q-C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b>0


(* ::Code:: *)
Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  q*(A+C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(2*A-C*q^2)-(A-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b>0


(* ::Code:: *)
Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  q/a*Int[(A*q+(A+B*q)*x)/(q^2+q*x+x^2),x] /;
 ZeroQ[A+B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b<0


(* ::Code:: *)
Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  B*q^2/a*Int[x/(q^2+q*x+x^2),x] /;
 ZeroQ[B*q+C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b<0


(* ::Code:: *)
Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  A*q/a*Int[(q+x)/(q^2+q*x+x^2),x] /;
 ZeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b<0


(* ::Code:: *)
Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  q*(A+B*q+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(q*(2*A-B*q-C*q^2)+(A+B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[A+B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b<0


(* ::Code:: *)
Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  q*(B*q+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(-q*(B*q+C*q^2)+(B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[B*q+C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b<0


(* ::Code:: *)
Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  q*(A+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(q*(2*A-C*q^2)+(A-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b<0


(* ::Code:: *)
Int[(A_+B_.*x_^m_)*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  A*Int[(a+b*x^n)^p,x] +
  B*Int[x^(n-1)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,A,B,m,n,p},x] && ZeroQ[m-n+1] (* && Not[EvenQ[n]] *)


(* ::Code:: *)
Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Coefficient[u,x,n-1]*Int[x^(n-1)*(a+b*x^n)^p,x] + 
  Int[ExpandToSum[u-Coefficient[u,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b,p},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && Exponent[u,x]==n-1


(* ::Code:: *)
Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*Sum[Coefficient[u,x,k]*x^k/(n*p+k+1),{k,0,n-2}]*(a+b*x^n)^p + 
  a*n*p*Int[Sum[Coefficient[u,x,k]*x^k/(n*p+k+1),{k,0,n-2}]*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && 0<Exponent[u,x]<n-1 && RationalQ[p] && p>0


(* ::Code:: *)
Int[u_/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{v=Sum[x^i*(Coefficient[u,x,i]+Coefficient[u,x,n/2+i]*x^(n/2))/(a+b*x^n),{i,0,n/2-1}]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n/2] && Exponent[u,x]<n-1


(* ::Code:: *)
Int[u_/(a_+b_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[u/(a+b*x^n),x],x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n]


(* ::Code:: *)
Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -x*u*(a+b*x^n)^(p+1)/(a*n*(p+1)) + 
  1/(a*n*(p+1))*Int[Sum[(n*(p+1)+k+1)*Coefficient[u,x,k]*x^k,{k,0,n-2}]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && 0<Exponent[u,x]<n-1 && RationalQ[p] && p<-1


(* ::Code:: *)
(* Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[Sum[Coefficient[u,x,k]*x^k,{k,0,n-2}]*(a+b*x^n)^p,x] + 
  Int[x^(n-1)*Sum[Coefficient[u,x,k]*x^(k-(n-1)),{k,n-1,Exponent[u,x]}]*(a+b*x^n)^p,x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && Exponent[u,x]>=n-1 && RationalQ[p] && p<-1 *)


(* ::Code:: *)
Int[x_^m_.*u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  u*(a+b*x^n)^(p+1)/(b*n*(p+1)) - 
  1/(b*n*(p+1))*Int[Sum[k*Coefficient[u,x,k]*x^(k-1),{k,1,Exponent[u,x]}]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && ZeroQ[m-(n-1)] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


(* ::Code:: *)
Int[x_^m_.*u_*(a_.+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{v=Sum[x^(m+i)*(Coefficient[u,x,i]+Coefficient[u,x,n/2+i]*x^(n/2))*(a+b*x^n)^p,{i,0,n/2-1}]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b,m},x] && PolynomialQ[u,x] && EvenQ[n] && NegativeIntegerQ[p] && 0<Exponent[u,x]<n


(* ::Code:: *)
Int[x_^m_.*u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[x^m*u*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,m},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && IntegersQ[m,p]


(* ::Code:: *)
Int[u_*(a_.+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  Int[Sum[x^i*(Coefficient[u,x,i]+Coefficient[u,x,n+i]*x^n)*(a+b*x^n+c*x^(2*n))^p,{i,0,n-1}],x] /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && PolynomialQ[u,x] && 1<Exponent[u,x]<2*n && 
  Not[BinomialQ[u,x]] && (NonzeroQ[p+1] || Not[NiceSqrtQ[b^2-4*a*c]]) && Not[MatchQ[u,x^m_ /; FreeQ[m,x]]]


(* ::Code:: *)
Int[x_^m_.*u_*(a_.+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  Int[Sum[x^(m+i)*(Coefficient[u,x,i]+Coefficient[u,x,n+i]*x^n)*(a+b*x^n+c*x^(2*n))^p,{i,0,n-1}],x] /;
FreeQ[{a,b,c,m,p},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && PolynomialQ[u,x] && 1<Exponent[u,x]<2*n && 
  Not[BinomialQ[u,x]] && (NonzeroQ[p+1] || Not[NiceSqrtQ[b^2-4*a*c]])


