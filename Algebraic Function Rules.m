(* ::Package:: *)

(* ::Section:: *)
(*Algebraic Binomial Function Rules*)


(* ::Subsection::Closed:: *)
(*u (a+b x+c x^2+d x^3)^p*)


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*a^(2*p))*Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d},x] && IntegerQ[p] && ZeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+b*x+d*x^3)^p,x],x] /;
FreeQ[{a,b,d},x] && PositiveIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+d*x^3]},
  Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p))*Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && ZeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+d*x^3]},
  (a+b*x+d*x^3)^p/Map[Function[#^p],u]*Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  (a+b*x+d*x^3)^p/(((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p)*
    Int[((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*a^(2*p))*Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,e,f,m},x] && IntegerQ[p] && ZeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(e+f*x)^m,(a+b*x+d*x^3)^p,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+d*x^3]},
  Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p))*Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+d*x^3]},
  (a+b*x+d*x^3)^p/Map[Function[#^p],u]*Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  (a+b*x+d*x^3)^p/(((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p)*
    Int[(e+f*x)^m*((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  -1/(3^(3*p)*d^(2*p))*Int[(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d},x] && IntegerQ[p] && ZeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+c*x^2+d*x^3]},
  Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+c*x^2+d*x^3)^p/((c-3*d*x)^p*(2*c+3*d*x)^(2*p))*Int[(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+c*x^2+d*x^3]},
  (a+c*x^2+d*x^3)^p/Map[Function[#^p],u]*Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  (a+c*x^2+d*x^3)^p/((c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  -1/(3^(3*p)*d^(2*p))*Int[(e+f*x)^m*(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(e+f*x)^m,(a+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+c*x^2+d*x^3]},
  Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+c*x^2+d*x^3)^p/((c-3*d*x)^p*(2*c+3*d*x)^(2*p))*Int[(e+f*x)^m*(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+c*x^2+d*x^3]},
  (a+c*x^2+d*x^3)^p/Map[Function[#^p],u]*Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  (a+c*x^2+d*x^3)^p/((c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(e+f*x)^m*(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Int[(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Subst[Int[(3*a*b*c-b^3+c^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[b^3-3*a*b*c,3]},
  1/(3^p*b^p*c^p)*Int[(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[c^3-3*b*c*d,3]},
  1/(3^p*b^p*c^p)*Int[(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+b*x+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+c*x^2+d*x^3]},
  Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+c*x^2+d*x^3)^p/(b+c*x)^(3*p)*Int[(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[b^3-3*a*b*c,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p)*
    Int[(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[c^3-3*b*c*d,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p)*
    Int[(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+c*x^2+d*x^3]},
  (a+b*x+c*x^2+d*x^3)^p/Map[Function[#^p],u]*Int[Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] *)


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


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && PolyQ[u,x,3] && Not[CubicMatchQ[u,x]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[b^3-3*a*b*c,3]},
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[c^3-3*b*c*d,3]},
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(e+f*x)^m,(a+b*x+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+c*x^2+d*x^3]},
  Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+c*x^2+d*x^3)^p/(b+c*x)^(3*p)*Int[(e+f*x)^m*(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[b^3-3*a*b*c,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p)*
    Int[(e+f*x)^m*(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{r=Rt[c^3-3*b*c*d,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p)*
    Int[(e+f*x)^m*(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Module[{u=Factor[a+b*x+c*x^2+d*x^3]},
  (a+b*x+c*x^2+d*x^3)^p/Map[Function[#^p],u]*Int[(e+f*x)^m*Map[Function[#^p],u],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] *)


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


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && LinearQ[u,x] && PolyQ[v,x,3] && Not[LinearMatchQ[u,x] && CubicMatchQ[v,x]]


(* ::Subsection::Closed:: *)
(*u (a+b x+c x^2+d x^3+e x^4)^p*)


Int[(f_+g_.*x_^2)/((d_+e_.*x_+d_.*x_^2)*Sqrt[a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4]),x_Symbol] :=
  a*f/(d*Rt[a^2*(2*a-c),2])*ArcTan[(a*b+(4*a^2+b^2-2*a*c)*x+a*b*x^2)/(2*Rt[a^2*(2*a-c),2]*Sqrt[a+b*x+c*x^2+b*x^3+a*x^4])] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[b*d-a*e] && ZeroQ[f+g] && PosQ[a^2*(2*a-c)]


Int[(f_+g_.*x_^2)/((d_+e_.*x_+d_.*x_^2)*Sqrt[a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4]),x_Symbol] :=
  -a*f/(d*Rt[-a^2*(2*a-c),2])*ArcTanh[(a*b+(4*a^2+b^2-2*a*c)*x+a*b*x^2)/(2*Rt[-a^2*(2*a-c),2]*Sqrt[a+b*x+c*x^2+b*x^3+a*x^4])] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[b*d-a*e] && ZeroQ[f+g] && NegQ[a^2*(2*a-c)]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  Subst[Int[SimplifyIntegrand[(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[d^3-4*c*d*e+8*b*e^2] && p=!=2 && p=!=3


Int[v_^p_,x_Symbol] :=
  Module[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  Subst[Int[SimplifyIntegrand[(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
 ZeroQ[d^3-4*c*d*e+8*b*e^2] && NonzeroQ[d]] /;
FreeQ[p,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && p=!=2 && p=!=3


Int[u_*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  Subst[Int[SimplifyIntegrand[ReplaceAll[u,x->-d/(4*e)+x]*(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
FreeQ[{a,b,c,d,e,p},x] && PolynomialQ[u,x] && ZeroQ[d^3-4*c*d*e+8*b*e^2] && Not[PositiveIntegerQ[p]]


Int[u_*v_^p_,x_Symbol] :=
  Module[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  Subst[Int[SimplifyIntegrand[ReplaceAll[u,x->-d/(4*e)+x]*(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
 ZeroQ[d^3-4*c*d*e+8*b*e^2] && NonzeroQ[d]] /;
FreeQ[p,x] && PolynomialQ[u,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && Not[PositiveIntegerQ[p]]


Int[(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  -16*a^2*Subst[
    Int[1/(b-4*a*x)^2*(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p,x],x,b/(4*a)+1/x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^3-4*a*b*c+8*a^2*d] && IntegerQ[2*p]


Int[v_^p_,x_Symbol] :=
  Module[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  -16*a^2*Subst[
    Int[1/(b-4*a*x)^2*(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p,x],x,b/(4*a)+1/x] /;
 NonzeroQ[a] && NonzeroQ[b] && ZeroQ[b^3-4*a*b*c+8*a^2*d]] /;
FreeQ[p,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && IntegerQ[2*p]


Int[(A_.+B_.*x_+C_.*x_^2+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[(b*A-2*a*B+2*a*D+A*q+(2*a*A-2*a*C+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[(b*A-2*a*B+2*a*D-A*q+(2*a*A-2*a*C+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,C,D},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


Int[(A_.+B_.*x_+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[(b*A-2*a*B+2*a*D+A*q+(2*a*A+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[(b*A-2*a*B+2*a*D-A*q+(2*a*A+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,D},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


Int[x_^m_.*(A_.+B_.*x_+C_.*x_^2+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[x^m*(b*A-2*a*B+2*a*D+A*q+(2*a*A-2*a*C+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[x^m*(b*A-2*a*B+2*a*D-A*q+(2*a*A-2*a*C+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,C,D,m},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


Int[x_^m_.*(A_.+B_.*x_+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[x^m*(b*A-2*a*B+2*a*D+A*q+(2*a*A+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[x^m*(b*A-2*a*B+2*a*D-A*q+(2*a*A+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,D,m},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


(* ::Subsection::Closed:: *)
(*Px (a+b x^n)^p*)


(* Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[Sum[Coefficient[u,x,k]*x^k,{k,0,n-2}]*(a+b*x^n)^p,x] + 
  Int[x^(n-1)*Sum[Coefficient[u,x,k]*x^(k-(n-1)),{k,n-1,Exponent[u,x]}]*(a+b*x^n)^p,x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && Exponent[u,x]>=n-1 && RationalQ[p] && p<-1 *)


Int[u_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[PolynomialQuotient[u,a+b*x^n,x]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,p},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && ZeroQ[PolynomialRemainder[u,a+b*x^n,x]]


Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Coefficient[u,x,n-1]*(a+b*x^n)^(p+1)/(b*n*(p+1)) + 
  Int[ExpandToSum[u-Coefficient[u,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n,p] && NonzeroQ[Coefficient[u,x,n-1]]


Int[u_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[u*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n,p] && ZeroQ[Coefficient[u,x,n-1]]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  B^3/b*Int[1/(A^2-A*B*x+B^2*x^2),x] /;
FreeQ[{a,b,A,B},x] && ZeroQ[a*B^3-b*A^3]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  -r*(B*r-A*s)/(3*a*s)*Int[1/(r+s*x),x] + 
  r/(3*a*s)*Int[(r*(B*r+2*A*s)+s*(B*r-A*s)*x)/(r^2-r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b,A,B},x] && NonzeroQ[a*B^3-b*A^3] && PosQ[a/b]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r*(B*r+A*s)/(3*a*s)*Int[1/(r-s*x),x] - 
  r/(3*a*s)*Int[(r*(B*r-2*A*s)-s*(B*r+A*s)*x)/(r^2+r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b,A,B},x] && NonzeroQ[a*B^3-b*A^3] && NegQ[a/b]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  C*q^3/a*Int[1/(q+x),x] + q^2*(A-C*q^2)/a*Int[1/(q^2-q*x+x^2),x] /;
 ZeroQ[A-B*q-2*C*q^2] && NonzeroQ[A-C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && PosQ[a/b]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  C*q^3/a*Int[1/(q+x),x] - C*q^4/a*Int[1/(q^2-q*x+x^2),x] /;
 ZeroQ[B+2*C*q]] /;
FreeQ[{a,b,B,C},x] && PosQ[a/b]


Int[(A_.+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  C*q^3/a*Int[1/(q+x),x] + C*q^4/a*Int[1/(q^2-q*x+x^2),x] /;
 ZeroQ[A-2*C*q^2]] /;
FreeQ[{a,b,A,C},x] && PosQ[a/b]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  C*q^3/a*Int[1/(q-x),x] + q^2*(A-C*q^2)/a*Int[1/(q^2+q*x+x^2),x] /;
 ZeroQ[A+B*q-2*C*q^2] && NonzeroQ[A-C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NegQ[a/b]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  C*q^3/a*Int[1/(q-x),x] - C*q^4/a*Int[1/(q^2+q*x+x^2),x] /;
 ZeroQ[B-2*C*q]] /;
FreeQ[{a,b,B,C},x] && NegQ[a/b]


Int[(A_.+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  C*q^3/a*Int[1/(q-x),x] + C*q^4/a*Int[1/(q^2+q*x+x^2),x] /;
 ZeroQ[A-2*C*q^2]] /;
FreeQ[{a,b,A,C},x] && NegQ[a/b]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Int[(A+B*x)/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,A,B,C},x] && (ZeroQ[a*B^3-b*A^3] || Not[RationalQ[a/b]])


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  B*Int[x/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,B,C},x] && Not[RationalQ[a/b]]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  A*Int[1/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,A,C},x] && Not[RationalQ[a,b,A,C]]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  q^2/a*Int[(A+C*q*x)/(q^2-q*x+x^2),x] /;
 ZeroQ[A-B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b>0


Int[(B_*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  B*q^2/a*Int[x/(q^2-q*x+x^2),x] /;
 ZeroQ[-B+C*q]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b>0


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  q^2/a*Int[(A+C*q*x)/(q^2-q*x+x^2),x] /;
 ZeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b>0


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  q*(A-B*q+C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(2*A+B*q-C*q^2)-(A-B*q-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[A-B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b>0


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  -q*(B*q-C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(B*q-C*q^2)+(B*q+2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[B*q-C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b>0


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(a/b)^(1/3)},
  q*(A+C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(2*A-C*q^2)-(A-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b>0


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  q/a*Int[(A*q+(A+B*q)*x)/(q^2+q*x+x^2),x] /;
 ZeroQ[A+B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b<0


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  B*q^2/a*Int[x/(q^2+q*x+x^2),x] /;
 ZeroQ[B*q+C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b<0


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  A*q/a*Int[(q+x)/(q^2+q*x+x^2),x] /;
 ZeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b<0


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  q*(A+B*q+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(q*(2*A-B*q-C*q^2)+(A+B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[A+B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b<0


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  q*(B*q+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(-q*(B*q+C*q^2)+(B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[B*q+C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b<0


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Module[{q=(-a/b)^(1/3)},
  q*(A+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(q*(2*A-C*q^2)+(A-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b<0


Int[(A_+B_.*x_^m_)*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  A*Int[(a+b*x^n)^p,x] +
  B*Int[x^(n-1)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,A,B,m,n,p},x] && ZeroQ[m-n+1] (* && Not[EvenQ[n]] *)


Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Coefficient[u,x,n-1]*Int[x^(n-1)*(a+b*x^n)^p,x] + 
  Int[ExpandToSum[u-Coefficient[u,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b,p},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && Exponent[u,x]==n-1


Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*Sum[Coefficient[u,x,k]*x^k/(n*p+k+1),{k,0,n-2}]*(a+b*x^n)^p + 
  a*n*p*Int[Sum[Coefficient[u,x,k]*x^k/(n*p+k+1),{k,0,n-2}]*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && 0<Exponent[u,x]<n-1 && RationalQ[p] && p>0


Int[u_/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{v=Sum[x^i*(Coefficient[u,x,i]+Coefficient[u,x,n/2+i]*x^(n/2))/(a+b*x^n),{i,0,n/2-1}]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n/2] && Exponent[u,x]<n-1


Int[u_/(a_+b_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[u/(a+b*x^n),x],x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n]


Int[u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -x*u*(a+b*x^n)^(p+1)/(a*n*(p+1)) + 
  1/(a*n*(p+1))*Int[Sum[(n*(p+1)+k+1)*Coefficient[u,x,k]*x^k,{k,0,n-2}]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && 0<Exponent[u,x]<n-1 && RationalQ[p] && p<-1


Int[x_^m_.*u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  u*(a+b*x^n)^(p+1)/(b*n*(p+1)) - 
  1/(b*n*(p+1))*Int[Sum[k*Coefficient[u,x,k]*x^(k-1),{k,1,Exponent[u,x]}]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && PolynomialQ[u,x] && ZeroQ[m-(n-1)] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[x_^m_.*u_*(a_.+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{v=Sum[x^(m+i)*(Coefficient[u,x,i]+Coefficient[u,x,n/2+i]*x^(n/2))*(a+b*x^n)^p,{i,0,n/2-1}]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b,m},x] && PolynomialQ[u,x] && EvenQ[n] && NegativeIntegerQ[p] && 0<Exponent[u,x]<n


Int[x_^m_.*u_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[x^m*u*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,m},x] && PolynomialQ[u,x] && PositiveIntegerQ[n] && IntegersQ[m,p]


Int[u_^m_.*(a_.+b_.*(c_+d_.*x_)^n_)^p_,x_Symbol] :=
  Module[{k=Denominator[n]},
  k/d*Subst[Int[SimplifyIntegrand[x^(k-1)*ReplaceAll[u,x->x^k/d-c/d]^m*(a+b*x^(k*n))^p,x],x],x,(c+d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && PolynomialQ[u,x] && IntegerQ[m] && RationalQ[n]


(* ::Subsection::Closed:: *)
(*Miscellaneous Algebraic Functions*)


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  c/(e*(b*c-a*d))*Int[(u*Sqrt[a+b*x])/x,x] - a/(f*(b*c-a*d))*Int[(u*Sqrt[c+d*x])/x,x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a*e^2-c*f^2]


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  -d/(e*(b*c-a*d))*Int[u*Sqrt[a+b*x],x] + b/(f*(b*c-a*d))*Int[u*Sqrt[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[b*e^2-d*f^2]


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  e*Int[(u*Sqrt[a+b*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x] - 
  f*Int[(u*Sqrt[c+d*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a*e^2-c*f^2] && NonzeroQ[b*e^2-d*f^2]


Int[u_./(d_.*x_^n_.+c_.*Sqrt[a_.+b_.*x_^p_.]),x_Symbol] :=
  -b/(a*d)*Int[u*x^n,x] + 1/(a*c)*Int[u*Sqrt[a+b*x^(2*n)],x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[p-2*n] && ZeroQ[b*c^2-d^2]


Int[x_^m_./(d_.*x_^n_.+c_.*Sqrt[a_.+b_.*x_^p_.]),x_Symbol] :=
  -d*Int[x^(m+n)/(a*c^2+(b*c^2-d^2)*x^(2*n)),x] + 
  c*Int[(x^m*Sqrt[a+b*x^(2*n)])/(a*c^2+(b*c^2-d^2)*x^(2*n)),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[p-2*n] && NonzeroQ[b*c^2-d^2]


Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d-(b*d-2*a*e)*x^2),x],x,x/Sqrt[a+b*x^2+c*x^4]] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[B*d+A*e] && ZeroQ[c*d^2-a*e^2]


Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d+2*a*e*x^2),x],x,x/Sqrt[a+c*x^4]] /;
FreeQ[{a,c,d,e,A,B},x] && ZeroQ[B*d+A*e] && ZeroQ[c*d^2-a*e^2]


Int[(A_+B_.*x_^4)/((d_+e_.*x_^2+f_.*x_^4)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d-(b*d-a*e)*x^2),x],x,x/Sqrt[a+b*x^2+c*x^4]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && ZeroQ[c*d-a*f] && ZeroQ[a*B+A*c]


Int[(A_+B_.*x_^4)/((d_+e_.*x_^2+f_.*x_^4)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d+a*e*x^2),x],x,x/Sqrt[a+c*x^4]] /;
FreeQ[{a,c,d,e,f,A,B},x] && ZeroQ[c*d-a*f] && ZeroQ[a*B+A*c]


Int[(A_+B_.*x_^4)/((d_+f_.*x_^4)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d-b*d*x^2),x],x,x/Sqrt[a+b*x^2+c*x^4]] /;
FreeQ[{a,b,c,d,f,A,B},x] && ZeroQ[c*d-a*f] && ZeroQ[a*B+A*c]


Int[(g_.+h_.*x_)*Sqrt[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  2*(f*(5*b*c*g^2-2*b^2*g*h-3*a*c*g*h+2*a*b*h^2)+c*f*(10*c*g^2-b*g*h+a*h^2)*x+9*c^2*f*g*h*x^2+3*c^2*f*h^2*x^3-
    (e*g-d*h)*(5*c*g-2*b*h+c*h*x)*Sqrt[a+b*x+c*x^2])/
  (15*c^2*f*(g+h*x))*Sqrt[d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && ZeroQ[(e*g-d*h)^2-f^2*(c*g^2-b*g*h+a*h^2)] && ZeroQ[2*e^2*g-2*d*e*h-f^2*(2*c*g-b*h)]


Int[(g_.+h_.*x_)^m_.*(u_+f_.*(j_.+k_.*Sqrt[v_]))^n_.,x_Symbol] :=
  Int[(g+h*x)^m*(ExpandToSum[u+f*j,x]+f*k*Sqrt[ExpandToSum[v,x]])^n,x] /;
FreeQ[{f,g,h,j,k,m,n},x] && LinearQ[u,x] && QuadraticQ[v,x] && 
  Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x] && (ZeroQ[j] || ZeroQ[f-1])] && 
  ZeroQ[(Coefficient[u,x,1]*g-h*(Coefficient[u,x,0]+f*j))^2-f^2*k^2*(Coefficient[v,x,2]*g^2-Coefficient[v,x,1]*g*h+Coefficient[v,x,0]*h^2)]


(* Int[1/(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  Int[(d+e*x)/(d^2-a*f^2+(2*d*e-b*f^2)*x),x] - 
  f*Int[Sqrt[a+b*x+c*x^2]/(d^2-a*f^2+(2*d*e-b*f^2)*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[e^2-c*f^2] *)


(* Int[1/(d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]),x_Symbol] :=
  Int[(d+e*x)/(d^2-a*f^2+2*d*e*x),x] - 
  f*Int[Sqrt[a+c*x^2]/(d^2-a*f^2+2*d*e*x),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[e^2-c*f^2] *)


Int[(g_.+h_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_)^p_.,x_Symbol] :=
  2*Subst[Int[(g+h*x^n)^p*(d^2*e-(b*d-a*e)*f^2-(2*d*e-b*f^2)*x+e*x^2)/(-2*d*e+b*f^2+2*e*x)^2,x],x,d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h,n},x] && ZeroQ[e^2-c*f^2] && IntegerQ[p]


Int[(g_.+h_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_)^p_.,x_Symbol] :=
  1/(2*e)*Subst[Int[(g+h*x^n)^p*(d^2+a*f^2-2*d*x+x^2)/(d-x)^2,x],x,d+e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e,f,g,h,n},x] && ZeroQ[e^2-c*f^2] && IntegerQ[p]


Int[(g_.+h_.*(u_+f_. Sqrt[v_])^n_)^p_.,x_Symbol] :=
  Int[(g+h*(ExpandToSum[u,x]+f*Sqrt[ExpandToSum[v,x]])^n)^p,x] /;
FreeQ[{f,g,h,n},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]] && 
  ZeroQ[Coefficient[u,x,1]^2-Coefficient[v,x,2]*f^2] && IntegerQ[p]


Int[(g_.+h_.*x_)^m_.*(e_.*x_+f_.*Sqrt[a_.+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(m+1)*e^(m+1))*Subst[Int[x^(n-m-2)*(a*f^2+x^2)*(-a*f^2*h+2*e*g*x+h*x^2)^m,x],x,e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,e,f,g,h,n},x] && ZeroQ[e^2-c*f^2] && IntegerQ[m]


Int[x_^p_.*(g_+i_.*x_^2)^m_.*(e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(2*m+p+1)*e^(p+1)*f^(2*m))*(i/c)^m*Subst[Int[x^(n-2*m-p-2)*(-a*f^2+x^2)^p*(a*f^2+x^2)^(2*m+1),x],x,e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,e,f,g,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && IntegersQ[p,2*m] && (IntegerQ[m] || PositiveQ[i/c])


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  2/f^(2*m)*(i/c)^m*
    Subst[Int[x^n*(d^2*e-(b*d-a*e)*f^2-(2*d*e-b*f^2)*x+e*x^2)^(2*m+1)/(-2*d*e+b*f^2+2*e*x)^(2*(m+1)),x],x,d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && ZeroQ[c*h-b*i] && IntegerQ[2*m] && (IntegerQ[m] || PositiveQ[i/c])


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(2*m+1)*e*f^(2*m))*(i/c)^m*
    Subst[Int[x^n*(d^2+a*f^2-2*d*x+x^2)^(2*m+1)/(-d+x)^(2*(m+1)),x],x,d+e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && IntegerQ[2*m] && (IntegerQ[m] || PositiveQ[i/c])


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m-1/2)*Sqrt[g+h*x+i*x^2]/Sqrt[a+b*x+c*x^2]*Int[(a+b*x+c*x^2)^m*(d+e*x+f*Sqrt[a+b*x+c*x^2])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && ZeroQ[c*h-b*i] && PositiveIntegerQ[m+1/2] && Not[PositiveQ[i/c]]


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m-1/2)*Sqrt[g+i*x^2]/Sqrt[a+c*x^2]*Int[(a+c*x^2)^m*(d+e*x+f*Sqrt[a+c*x^2])^n,x] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && PositiveIntegerQ[m+1/2] && Not[PositiveQ[i/c]]


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m+1/2)*Sqrt[a+b*x+c*x^2]/Sqrt[g+h*x+i*x^2]*Int[(a+b*x+c*x^2)^m*(d+e*x+f*Sqrt[a+b*x+c*x^2])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && ZeroQ[c*h-b*i] && NegativeIntegerQ[m-1/2] && Not[PositiveQ[i/c]]


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m+1/2)*Sqrt[a+c*x^2]/Sqrt[g+i*x^2]*Int[(a+c*x^2)^m*(d+e*x+f*Sqrt[a+c*x^2])^n,x] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && NegativeIntegerQ[m-1/2] && Not[PositiveQ[i/c]]


Int[w_^m_.*(u_+f_.*(j_.+k_.*Sqrt[v_]))^n_.,x_Symbol] :=
  Int[ExpandToSum[w,x]^m*(ExpandToSum[u+f*j,x]+f*k*Sqrt[ExpandToSum[v,x]])^n,x] /;
FreeQ[{f,j,k,m,n},x] && LinearQ[u,x] && QuadraticQ[{v,w},x] && 
  Not[LinearMatchQ[u,x] && QuadraticMatchQ[{v,w},x] && (ZeroQ[j] || ZeroQ[f-1])] && 
  ZeroQ[Coefficient[u,x,1]^2-Coefficient[v,x,2]*f^2*k^2]


Int[1/((a_+b_.*x_^n_.)*Sqrt[c_.*x_^2+d_.*(a_+b_.*x_^n_.)^p_.]),x_Symbol] :=
  1/a*Subst[Int[1/(1-c*x^2),x],x,x/Sqrt[c*x^2+d*(a+b*x^n)^(2/n)]] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[p-2/n]


Int[Sqrt[a_+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
  2*b^2*d*x^3/(3*(a+b*Sqrt[c+d*x^2])^(3/2)) + 2*a*x/Sqrt[a+b*Sqrt[c+d*x^2]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2*c]


Int[Sqrt[a_.*x_^2+b_.*x_*Sqrt[c_+d_.*x_^2]]/(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[2]*b/a*Subst[Int[1/Sqrt[1+x^2/a],x],x,a*x+b*Sqrt[c+d*x^2]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2*d] && ZeroQ[b^2*c+a]


Int[Sqrt[e_.*x_*(a_.*x_+b_.*Sqrt[c_+d_.*x_^2])]/(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Int[Sqrt[a*e*x^2+b*e*x*Sqrt[c+d*x^2]]/(x*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2*d] && ZeroQ[b^2*c*e+a]


Int[Sqrt[c_.*x_^2+d_.*Sqrt[a_+b_.*x_^4]]/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  d*Subst[Int[1/(1-2*c*x^2),x],x,x/Sqrt[c*x^2+d*Sqrt[a+b*x^4]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[c^2-b*d^2]


Int[(c_.+d_.*x_)^m_.*Sqrt[b_.*x_^2+Sqrt[a_+e_.*x_^4]]/Sqrt[a_+e_.*x_^4],x_Symbol] :=
  (1-I)/2*Int[(c+d*x)^m/Sqrt[Sqrt[a]-I*b*x^2],x] +
  (1+I)/2*Int[(c+d*x)^m/Sqrt[Sqrt[a]+I*b*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[e-b^2] && PositiveQ[a]


Int[(A_+B_.*x_^n_)/(a_+b_.*x_^2+c_.*x_^n_+d_.*x_^j_), x_Symbol] :=
  A^2*(n-1)*Subst[Int[1/(a+A^2*b*(n-1)^2*x^2),x],x,x/(A*(n-1)-B*x^n)] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[j-2*n] && NonzeroQ[n-2] && ZeroQ[a*B^2-A^2*d*(n-1)^2] && ZeroQ[B*c+2*A*d*(n-1)]


Int[x_^m_.*(A_+B_.*x_^n_.)/(a_+b_.*x_^k_.+c_.*x_^n_.+d_.*x_^j_), x_Symbol] :=
  A^2*(m-n+1)/(m+1)*Subst[Int[1/(a+A^2*b*(m-n+1)^2*x^2),x],x,x^(m+1)/(A*(m-n+1)+B*(m+1)*x^n)] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[j-2*n] && ZeroQ[k-2*(m+1)] && ZeroQ[a*B^2*(m+1)^2-A^2*d*(m-n+1)^2] && ZeroQ[B*c*(m+1)-2*A*d*(m-n+1)]


Int[u_*(a_.+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  Int[Sum[x^i*(Coefficient[u,x,i]+Coefficient[u,x,n+i]*x^n)*(a+b*x^n+c*x^(2*n))^p,{i,0,n-1}],x] /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && PolynomialQ[u,x] && 1<Exponent[u,x]<2*n && 
  Not[BinomialQ[u,x]] && (NonzeroQ[p+1] || Not[NiceSqrtQ[b^2-4*a*c]]) && Not[MatchQ[u,x^m_ /; FreeQ[m,x]]]


Int[x_^m_.*u_*(a_.+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  Int[Sum[x^(m+i)*(Coefficient[u,x,i]+Coefficient[u,x,n+i]*x^n)*(a+b*x^n+c*x^(2*n))^p,{i,0,n-1}],x] /;
FreeQ[{a,b,c,m,p},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && PolynomialQ[u,x] && 1<Exponent[u,x]<2*n && 
  Not[BinomialQ[u,x]] && (NonzeroQ[p+1] || Not[NiceSqrtQ[b^2-4*a*c]])
