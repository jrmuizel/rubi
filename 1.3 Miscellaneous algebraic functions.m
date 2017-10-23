(* ::Package:: *)

(* ::Section:: *)
(*1.3 Miscellaneous algebraic functions integration rules*)


(* ::Subsection::Closed:: *)
(*1.3.1 u (a+b x+c x^2+d x^3)^p*)


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*a^(2*p))*Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d},x] && IntegerQ[p] && EqQ[4*b^3+27*a^2*d,0]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+b*x+d*x^3)^p,x],x] /;
FreeQ[{a,b,d},x] && IGtQ[p,0] && NeQ[4*b^3+27*a^2*d,0]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+b*x+d*x^3]},
  FreeFactors[u,x]^p*Int[DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d},x] && ILtQ[p,0] && NeQ[4*b^3+27*a^2*d,0]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d},x] && ILtQ[p,0] && NeQ[4*b^3+27*a^2*d,0]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p))*Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && EqQ[4*b^3+27*a^2*d,0]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+b*x+d*x^3],x]},
  (a+b*x+d*x^3)^p/DistributeDegree[u,p]*Int[DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && NeQ[4*b^3+27*a^2*d,0]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  (a+b*x+d*x^3)^p/(((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p)*
    Int[((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && NeQ[4*b^3+27*a^2*d,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*a^(2*p))*Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,e,f,m},x] && IntegerQ[p] && EqQ[4*b^3+27*a^2*d,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+b*x+d*x^3)^p,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && IGtQ[p,0] && NeQ[4*b^3+27*a^2*d,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+b*x+d*x^3]},
  FreeFactors[u,x]^p*Int[(e+f*x)^m*DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d,e,f,m},x] && ILtQ[p,0] && NeQ[4*b^3+27*a^2*d,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,e,f,m},x] && ILtQ[p,0] && NeQ[4*b^3+27*a^2*d,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p))*Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && EqQ[4*b^3+27*a^2*d,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+b*x+d*x^3],x]},
  (a+b*x+d*x^3)^p/DistributeDegree[u,p]*Int[(e+f*x)^m*DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && NeQ[4*b^3+27*a^2*d,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  (a+b*x+d*x^3)^p/(((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p)*
    Int[(e+f*x)^m*((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && NeQ[4*b^3+27*a^2*d,0]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  -1/(3^(3*p)*d^(2*p))*Int[(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d},x] && IntegerQ[p] && EqQ[4*c^3+27*a*d^2,0]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,c,d},x] && IGtQ[p,0] && NeQ[4*c^3+27*a*d^2,0]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+c*x^2+d*x^3]},
  FreeFactors[u,x]^p*Int[DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d},x] && ILtQ[p,0] && NeQ[4*c^3+27*a*d^2,0]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d},x] && ILtQ[p,0] && NeQ[4*c^3+27*a*d^2,0]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+c*x^2+d*x^3)^p/((c-3*d*x)^p*(2*c+3*d*x)^(2*p))*Int[(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && EqQ[4*c^3+27*a*d^2,0]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+c*x^2+d*x^3],x]},
  (a+c*x^2+d*x^3)^p/DistributeDegree[u,p]*Int[DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && NeQ[4*c^3+27*a*d^2,0]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  (a+c*x^2+d*x^3)^p/((c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && NeQ[4*c^3+27*a*d^2,0]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  -1/(3^(3*p)*d^(2*p))*Int[(e+f*x)^m*(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,e,f,m},x] && IntegerQ[p] && EqQ[4*c^3+27*a*d^2,0]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && IGtQ[p,0] && NeQ[4*c^3+27*a*d^2,0]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+c*x^2+d*x^3]},
  FreeFactors[u,x]^p*Int[(e+f*x)^m*DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d,e,f,m},x] && ILtQ[p,0] && NeQ[4*c^3+27*a*d^2,0]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,e,f,m},x] && ILtQ[p,0] && NeQ[4*c^3+27*a*d^2,0]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+c*x^2+d*x^3)^p/((c-3*d*x)^p*(2*c+3*d*x)^(2*p))*Int[(e+f*x)^m*(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && EqQ[4*c^3+27*a*d^2,0]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+c*x^2+d*x^3],x]},
  (a+c*x^2+d*x^3)^p/DistributeDegree[u,p]*Int[(e+f*x)^m*DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NeQ[4*c^3+27*a*d^2,0]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  (a+c*x^2+d*x^3)^p/((c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(e+f*x)^m*(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NeQ[4*c^3+27*a*d^2,0]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Int[(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && EqQ[c^2-3*b*d,0] && EqQ[b^2-3*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Subst[Int[(3*a*b*c-b^3+c^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && EqQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[b^3-3*a*b*c,3]},
  1/(3^p*b^p*c^p)*Int[(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && EqQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0] *)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[c^3-3*b*c*d,3]},
  1/(3^p*b^p*c^p)*Int[(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NeQ[c^2-3*b*d,0] && EqQ[b^2-3*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+b*x+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+b*x+c*x^2+d*x^3]},
  FreeFactors[u,x]^p*Int[DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0] *)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+c*x^2+d*x^3)^p/(b+c*x)^(3*p)*Int[(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && EqQ[c^2-3*b*d,0] && EqQ[b^2-3*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[b^3-3*a*b*c,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p)*
    Int[(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && EqQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[c^3-3*b*c*d,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p)*
    Int[(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NeQ[c^2-3*b*d,0] && EqQ[b^2-3*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+b*x+c*x^2+d*x^3],x]},
  (a+b*x+c*x^2+d*x^3)^p/DistributeDegree[u,p]*Int[DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] *)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  (a+b*x+c*x^2+d*x^3)^p/
    ((c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && PolyQ[u,x,3] && Not[CubicMatchQ[u,x]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && EqQ[c^2-3*b*d,0] && EqQ[b^2-3*a*c,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[b^3-3*a*b*c,3]},
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && EqQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[c^3-3*b*c*d,3]},
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && NeQ[c^2-3*b*d,0] && EqQ[b^2-3*a*c,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+b*x+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+b*x+c*x^2+d*x^3]},
  FreeFactors[u,x]^p*Int[(e+f*x)^m*DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d,e,f,m},x] && ILtQ[p,0] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,e,f,m},x] && ILtQ[p,0] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


(* Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && ILtQ[p,0] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0] *)


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+c*x^2+d*x^3)^p/(b+c*x)^(3*p)*Int[(e+f*x)^m*(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && EqQ[c^2-3*b*d,0] && EqQ[b^2-3*a*c,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[b^3-3*a*b*c,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p)*
    Int[(e+f*x)^m*(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && EqQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[c^3-3*b*c*d,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p)*
    Int[(e+f*x)^m*(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NeQ[c^2-3*b*d,0] && EqQ[b^2-3*a*c,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+b*x+c*x^2+d*x^3],x]},
  (a+b*x+c*x^2+d*x^3)^p/DistributeDegree[u,p]*Int[(e+f*x)^m*DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


(* Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] *)


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  (a+b*x+c*x^2+d*x^3)^p/
    ((c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(e+f*x)^m*(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NeQ[c^2-3*b*d,0] && NeQ[b^2-3*a*c,0]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && LinearQ[u,x] && PolyQ[v,x,3] && Not[LinearMatchQ[u,x] && CubicMatchQ[v,x]]


(* ::Subsection::Closed:: *)
(*1.3.2 u (a+b x+c x^2+d x^3+e x^4)^p*)


Int[(f_+g_.*x_^2)/((d_+e_.*x_+d_.*x_^2)*Sqrt[a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4]),x_Symbol] :=
  a*f/(d*Rt[a^2*(2*a-c),2])*ArcTan[(a*b+(4*a^2+b^2-2*a*c)*x+a*b*x^2)/(2*Rt[a^2*(2*a-c),2]*Sqrt[a+b*x+c*x^2+b*x^3+a*x^4])] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*d-a*e,0] && EqQ[f+g,0] && PosQ[a^2*(2*a-c)]


Int[(f_+g_.*x_^2)/((d_+e_.*x_+d_.*x_^2)*Sqrt[a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4]),x_Symbol] :=
  -a*f/(d*Rt[-a^2*(2*a-c),2])*ArcTanh[(a*b+(4*a^2+b^2-2*a*c)*x+a*b*x^2)/(2*Rt[-a^2*(2*a-c),2]*Sqrt[a+b*x+c*x^2+b*x^3+a*x^4])] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*d-a*e,0] && EqQ[f+g,0] && NegQ[a^2*(2*a-c)]


Int[P3_/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Sqrt[8*a^2+b^2-4*a*c],A=Coeff[P3,x,0],B=Coeff[P3,x,1],C=Coeff[P3,x,2],D=Coeff[P3,x,3]},
  1/q*Int[(b*A-2*a*B+2*a*D+A*q+(2*a*A-2*a*C+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[(b*A-2*a*B+2*a*D-A*q+(2*a*A-2*a*C+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c},x] && PolyQ[P3,x,3] && EqQ[a,e] && EqQ[b,d] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


Int[x_^m_.*P3_/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Sqrt[8*a^2+b^2-4*a*c],A=Coeff[P3,x,0],B=Coeff[P3,x,1],C=Coeff[P3,x,2],D=Coeff[P3,x,3]},
  1/q*Int[x^m*(b*A-2*a*B+2*a*D+A*q+(2*a*A-2*a*C+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[x^m*(b*A-2*a*B+2*a*D-A*q+(2*a*A-2*a*C+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,m},x] && PolyQ[P3,x,3] && EqQ[a,e] && EqQ[b,d] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


Int[P4_^p_,x_Symbol] :=
  With[{a=Coeff[P4,x,0],b=Coeff[P4,x,1],c=Coeff[P4,x,2],d=Coeff[P4,x,3],e=Coeff[P4,x,4]},
  Subst[Int[SimplifyIntegrand[(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
 EqQ[d^3-4*c*d*e+8*b*e^2,0] && NeQ[d,0]] /;
FreeQ[p,x] && PolyQ[P4,x,4] && NeQ[p,2] && NeQ[p,3]


Int[Pq_*Q4_^p_,x_Symbol] :=
  With[{a=Coeff[Q4,x,0],b=Coeff[Q4,x,1],c=Coeff[Q4,x,2],d=Coeff[Q4,x,3],e=Coeff[Q4,x,4]},
  Subst[Int[SimplifyIntegrand[ReplaceAll[Pq,x->-d/(4*e)+x]*(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
 EqQ[d^3-4*c*d*e+8*b*e^2,0] && NeQ[d,0]] /;
FreeQ[p,x] && PolyQ[Pq,x] && PolyQ[Q4,x,4] && Not[IGtQ[p,0]]


Int[P4_^p_,x_Symbol] :=
  With[{a=Coeff[P4,x,0],b=Coeff[P4,x,1],c=Coeff[P4,x,2],d=Coeff[P4,x,3],e=Coeff[P4,x,4]},
  -16*a^2*Subst[
    Int[1/(b-4*a*x)^2*(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p,x],
    x,b/(4*a)+1/x] /;
 NeQ[a,0] && NeQ[b,0] && EqQ[b^3-4*a*b*c+8*a^2*d,0]] /;
FreeQ[p,x] && PolyQ[P4,x,4] && IntegerQ[2*p]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Rt[C*(2*e*(B*d-4*A*e)+C*(d^2-4*c*e)),2]},
  -2*C^2/q*ArcTanh[(C*d-B*e+2*C*e*x)/q] + 
  2*C^2/q*ArcTanh[C*(4*B*c*C-3*B^2*d-4*A*C*d+12*A*B*e+4*C*(2*c*C-B*d+2*A*e)*x+4*C*(2*C*d-B*e)*x^2+8*C^2*e*x^3)/(q*(B^2-4*A*C))]] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && EqQ[B^2*d+2*C*(b*C+A*d)-2*B*(c*C+2*A*e),0] && 
  EqQ[2*B^2*c*C-8*a*C^3-B^3*d-4*A*B*C*d+4*A*(B^2+2*A*C)*e,0] && PosQ[C*(2*e*(B*d-4*A*e)+C*(d^2-4*c*e))]


Int[(A_.+C_.*x_^2)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Rt[C*(-8*A*e^2+C*(d^2-4*c*e)),2]},
  -2*C^2/q*ArcTanh[C*(d+2*e*x)/q] + 2*C^2/q*ArcTanh[C*(A*d-2*(c*C+A*e)*x-2*C*d*x^2-2*C*e*x^3)/(A*q)]] /;
FreeQ[{a,b,c,d,e,A,C},x] && EqQ[b*C+A*d,0] && EqQ[a*C^2-A^2*e,0] && PosQ[C*(-8*A*e^2+C*(d^2-4*c*e))]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Rt[-C*(2*e*(B*d-4*A*e)+C*(d^2-4*c*e)),2]},
  2*C^2/q*ArcTan[(C*d-B*e+2*C*e*x)/q] - 
  2*C^2/q*ArcTan[C*(4*B*c*C-3*B^2*d-4*A*C*d+12*A*B*e+4*C*(2*c*C-B*d+2*A*e)*x+4*C*(2*C*d-B*e)*x^2+8*C^2*e*x^3)/(q*(B^2-4*A*C))]] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && EqQ[B^2*d+2*C*(b*C+A*d)-2*B*(c*C+2*A*e),0] && 
  EqQ[2*B^2*c*C-8*a*C^3-B^3*d-4*A*B*C*d+4*A*(B^2+2*A*C)*e,0] && NegQ[C*(2*e*(B*d-4*A*e)+C*(d^2-4*c*e))]


Int[(A_.+C_.*x_^2)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Rt[-C*(-8*A*e^2+C*(d^2-4*c*e)),2]},
  2*C^2/q*ArcTan[(C*d+2*C*e*x)/q] - 2*C^2/q*ArcTan[-C*(-A*d+2*(c*C+A*e)*x+2*C*d*x^2+2*C*e*x^3)/(A*q)]] /;
FreeQ[{a,b,c,d,e,A,C},x] && EqQ[b*C+A*d,0] && EqQ[a*C^2-A^2*e,0] && NegQ[C*(-8*A*e^2+C*(d^2-4*c*e))]


Int[P3_/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{A=Coeff[P3,x,0],B=Coeff[P3,x,1],C=Coeff[P3,x,2],D=Coeff[P3,x,3]},
    D/(4*e)*Log[a+b*x+c*x^2+d*x^3+e*x^4] - 
    1/(4*e)*Int[(b*D-4*A*e+2*(c*D-2*B*e)*x+(3*d*D-4*C*e)*x^2)/(a+b*x+c*x^2+d*x^3+e*x^4),x] /;
   EqQ[4*d*(c*D-2*B*e)^2+8*(3*d*D-4*C*e)*(b*d*D-b*C*e-A*d*e)-4*(c*D-2*B*e)*(3*c*d*D-4*c*C*e+2*b*D*e-8*A*e^2),0] && 
   EqQ[8*d*(c*D-2*B*e)^3+8*d*(b*D-4*A*e)*(c*D-2*B*e)*(3*d*D-4*C*e)+8*a*(3*d*D-4*C*e)^3-8*c*(c*D-2*B*e)^2*(3*d*D-4*C*e)-
     4*e*(b*D-4*A*e)*(4*(c*D-2*B*e)^2+2*(b*D-4*A*e)*(3*d*D-4*C*e)),0]] /;
FreeQ[{a,b,c,d,e},x] && PolyQ[P3,x,3]


(* ::Subsection::Closed:: *)
(*1.3.3 Miscellaneous algebraic functions*)


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  c/(e*(b*c-a*d))*Int[(u*Sqrt[a+b*x])/x,x] - a/(f*(b*c-a*d))*Int[(u*Sqrt[c+d*x])/x,x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a*e^2-c*f^2,0]


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  -d/(e*(b*c-a*d))*Int[u*Sqrt[a+b*x],x] + b/(f*(b*c-a*d))*Int[u*Sqrt[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[b*e^2-d*f^2,0]


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  e*Int[(u*Sqrt[a+b*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x] - 
  f*Int[(u*Sqrt[c+d*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[a*e^2-c*f^2,0] && NeQ[b*e^2-d*f^2,0]


Int[u_./(d_.*x_^n_.+c_.*Sqrt[a_.+b_.*x_^p_.]),x_Symbol] :=
  -b/(a*d)*Int[u*x^n,x] + 1/(a*c)*Int[u*Sqrt[a+b*x^(2*n)],x] /;
FreeQ[{a,b,c,d,n},x] && EqQ[p,2*n] && EqQ[b*c^2-d^2,0]


Int[x_^m_./(d_.*x_^n_.+c_.*Sqrt[a_.+b_.*x_^p_.]),x_Symbol] :=
  -d*Int[x^(m+n)/(a*c^2+(b*c^2-d^2)*x^(2*n)),x] + 
  c*Int[(x^m*Sqrt[a+b*x^(2*n)])/(a*c^2+(b*c^2-d^2)*x^(2*n)),x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[p,2*n] && NeQ[b*c^2-d^2,0]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  r/(3*a)*Int[1/((r+s*x)*Sqrt[d+e*x+f*x^2]),x] +
  r/(3*a)*Int[(2*r-s*x)/((r^2-r*s*x+s^2*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,d,e,f},x] && PosQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  r/(3*a)*Int[1/((r+s*x)*Sqrt[d+f*x^2]),x] +
  r/(3*a)*Int[(2*r-s*x)/((r^2-r*s*x+s^2*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,d,f},x] && PosQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r/(3*a)*Int[1/((r-s*x)*Sqrt[d+e*x+f*x^2]),x] +
  r/(3*a)*Int[(2*r+s*x)/((r^2+r*s*x+s^2*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,d,e,f},x] && NegQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r/(3*a)*Int[1/((r-s*x)*Sqrt[d+f*x^2]),x] +
  r/(3*a)*Int[(2*r+s*x)/((r^2+r*s*x+s^2*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,d,f},x] && NegQ[a/b]


Int[1/((d_+e_.*x_)*Sqrt[v_]),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*Sqrt[v]),x] - e*Int[x/((d^2-e^2*x^2)*Sqrt[v]),x] /;
FreeQ[{d,e},x] && PolyQ[v,x^2,2]


Int[1/((d_+e_.*x_)^2*Sqrt[v_]),x_Symbol] :=
  With[{a=Coeff[v,x,0],b=Coeff[v,x,2],c=Coeff[v,x,4]},
  -e^3*Sqrt[v]/((c*d^4+b*d^2*e^2+a*e^4)*(d+e*x)) - c/(c*d^4+b*d^2*e^2+a*e^4)*Int[(d^2-e^2*x^2)/Sqrt[v],x] /;
 NeQ[c*d^4+b*d^2*e^2+a*e^4,0] && EqQ[2*c*d^3+b*d*e^2,0]] /;
FreeQ[{d,e},x] && PolyQ[v,x^2,2]


Int[1/((d_+e_.*x_)^2*Sqrt[v_]),x_Symbol] :=
  With[{a=Coeff[v,x,0],b=Coeff[v,x,2],c=Coeff[v,x,4]},
  -e^3*Sqrt[v]/((c*d^4+b*d^2*e^2+a*e^4)*(d+e*x)) - 
  c/(c*d^4+b*d^2*e^2+a*e^4)*Int[(d^2-e^2*x^2)/Sqrt[v],x] + 
  (2*c*d^3+b*d*e^2)/(c*d^4+b*d^2*e^2+a*e^4)*Int[1/((d+e*x)*Sqrt[v]),x] /;
 NeQ[c*d^4+b*d^2*e^2+a*e^4,0] && NeQ[2*c*d^3+b*d*e^2,0]] /;
FreeQ[{d,e},x] && PolyQ[v,x^2,2]


Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[v_]),x_Symbol] :=
  With[{a=Coeff[v,x,0],b=Coeff[v,x,2],c=Coeff[v,x,4]},
  A*Subst[Int[1/(d-(b*d-2*a*e)*x^2),x],x,x/Sqrt[v]] /;
 EqQ[B*d+A*e,0] && EqQ[c*d^2-a*e^2,0]] /;
FreeQ[{d,e,A,B},x] && PolyQ[v,x^2,2]


Int[u_*(A_+B_.*x_^4)/Sqrt[v_],x_Symbol] :=
  With[{a=Coeff[v,x,0],b=Coeff[v,x,2],c=Coeff[v,x,4],d=Coeff[1/u,x,0],e=Coeff[1/u,x,2],f=Coeff[1/u,x,4]},
  A*Subst[Int[1/(d-(b*d-a*e)*x^2),x],x,x/Sqrt[v]] /;
 EqQ[a*B+A*c,0] && EqQ[c*d-a*f,0]] /;
FreeQ[{A,B},x] && PolyQ[v,x^2,2] && PolyQ[1/u,x^2,2]


Int[Sqrt[v_]/(d_+e_.*x_^4),x_Symbol] :=
  With[{a=Coeff[v,x,0],b=Coeff[v,x,2],c=Coeff[v,x,4]},
  a/d*Subst[Int[1/(1-2*b*x^2+(b^2-4*a*c)*x^4),x],x,x/Sqrt[v]] /;
 EqQ[c*d+a*e,0] && PosQ[a*c]] /;
FreeQ[{d,e},x] && PolyQ[v,x^2,2]


Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^4),x_Symbol] :=
  With[{q=Sqrt[b^2-4*a*c]},
  -a*Sqrt[b+q]/(2*Sqrt[2]*Rt[-a*c,2]*d)*ArcTan[Sqrt[b+q]*x*(b-q+2*c*x^2)/(2*Sqrt[2]*Rt[-a*c,2]*Sqrt[a+b*x^2+c*x^4])] + 
  a*Sqrt[-b+q]/(2*Sqrt[2]*Rt[-a*c,2]*d)*ArcTanh[Sqrt[-b+q]*x*(b+q+2*c*x^2)/(2*Sqrt[2]*Rt[-a*c,2]*Sqrt[a+b*x^2+c*x^4])]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c*d+a*e,0] && NegQ[a*c]


Int[1/((a_+b_.*x_)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  a*Int[1/((a^2-b^2*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] - b*Int[x/((a^2-b^2*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x]


Int[(g_.+h_.*x_)*Sqrt[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  2*(f*(5*b*c*g^2-2*b^2*g*h-3*a*c*g*h+2*a*b*h^2)+c*f*(10*c*g^2-b*g*h+a*h^2)*x+9*c^2*f*g*h*x^2+3*c^2*f*h^2*x^3-
    (e*g-d*h)*(5*c*g-2*b*h+c*h*x)*Sqrt[a+b*x+c*x^2])/
  (15*c^2*f*(g+h*x))*Sqrt[d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[(e*g-d*h)^2-f^2*(c*g^2-b*g*h+a*h^2),0] && EqQ[2*e^2*g-2*d*e*h-f^2*(2*c*g-b*h),0]


Int[(g_.+h_.*x_)^m_.*(u_+f_.*(j_.+k_.*Sqrt[v_]))^n_.,x_Symbol] :=
  Int[(g+h*x)^m*(ExpandToSum[u+f*j,x]+f*k*Sqrt[ExpandToSum[v,x]])^n,x] /;
FreeQ[{f,g,h,j,k,m,n},x] && LinearQ[u,x] && QuadraticQ[v,x] && 
  Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x] && (EqQ[j,0] || EqQ[f,1])] && 
  EqQ[(Coefficient[u,x,1]*g-h*(Coefficient[u,x,0]+f*j))^2-f^2*k^2*(Coefficient[v,x,2]*g^2-Coefficient[v,x,1]*g*h+Coefficient[v,x,0]*h^2),0]


(* Int[1/(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  Int[(d+e*x)/(d^2-a*f^2+(2*d*e-b*f^2)*x),x] - 
  f*Int[Sqrt[a+b*x+c*x^2]/(d^2-a*f^2+(2*d*e-b*f^2)*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e^2-c*f^2,0] *)


(* Int[1/(d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]),x_Symbol] :=
  Int[(d+e*x)/(d^2-a*f^2+2*d*e*x),x] - 
  f*Int[Sqrt[a+c*x^2]/(d^2-a*f^2+2*d*e*x),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[e^2-c*f^2,0] *)


Int[(g_.+h_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_)^p_.,x_Symbol] :=
  2*Subst[Int[(g+h*x^n)^p*(d^2*e-(b*d-a*e)*f^2-(2*d*e-b*f^2)*x+e*x^2)/(-2*d*e+b*f^2+2*e*x)^2,x],x,d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h,n},x] && EqQ[e^2-c*f^2,0] && IntegerQ[p]


Int[(g_.+h_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_)^p_.,x_Symbol] :=
  1/(2*e)*Subst[Int[(g+h*x^n)^p*(d^2+a*f^2-2*d*x+x^2)/(d-x)^2,x],x,d+e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e,f,g,h,n},x] && EqQ[e^2-c*f^2,0] && IntegerQ[p]


Int[(g_.+h_.*(u_+f_. Sqrt[v_])^n_)^p_.,x_Symbol] :=
  Int[(g+h*(ExpandToSum[u,x]+f*Sqrt[ExpandToSum[v,x]])^n)^p,x] /;
FreeQ[{f,g,h,n},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]] && 
  EqQ[Coefficient[u,x,1]^2-Coefficient[v,x,2]*f^2,0] && IntegerQ[p]


Int[(g_.+h_.*x_)^m_.*(e_.*x_+f_.*Sqrt[a_.+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(m+1)*e^(m+1))*Subst[Int[x^(n-m-2)*(a*f^2+x^2)*(-a*f^2*h+2*e*g*x+h*x^2)^m,x],x,e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,e,f,g,h,n},x] && EqQ[e^2-c*f^2,0] && IntegerQ[m]


Int[x_^p_.*(g_+i_.*x_^2)^m_.*(e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(2*m+p+1)*e^(p+1)*f^(2*m))*(i/c)^m*Subst[Int[x^(n-2*m-p-2)*(-a*f^2+x^2)^p*(a*f^2+x^2)^(2*m+1),x],x,e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,e,f,g,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && IntegersQ[p,2*m] && (IntegerQ[m] || GtQ[i/c,0])


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  2/f^(2*m)*(i/c)^m*
    Subst[Int[x^n*(d^2*e-(b*d-a*e)*f^2-(2*d*e-b*f^2)*x+e*x^2)^(2*m+1)/(-2*d*e+b*f^2+2*e*x)^(2*(m+1)),x],x,d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && EqQ[c*h-b*i,0] && IntegerQ[2*m] && (IntegerQ[m] || GtQ[i/c,0])


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(2*m+1)*e*f^(2*m))*(i/c)^m*
    Subst[Int[x^n*(d^2+a*f^2-2*d*x+x^2)^(2*m+1)/(-d+x)^(2*(m+1)),x],x,d+e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && IntegerQ[2*m] && (IntegerQ[m] || GtQ[i/c,0])


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m-1/2)*Sqrt[g+h*x+i*x^2]/Sqrt[a+b*x+c*x^2]*Int[(a+b*x+c*x^2)^m*(d+e*x+f*Sqrt[a+b*x+c*x^2])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && EqQ[c*h-b*i,0] && IGtQ[m+1/2,0] && Not[GtQ[i/c,0]]


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m-1/2)*Sqrt[g+i*x^2]/Sqrt[a+c*x^2]*Int[(a+c*x^2)^m*(d+e*x+f*Sqrt[a+c*x^2])^n,x] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && IGtQ[m+1/2,0] && Not[GtQ[i/c,0]]


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m+1/2)*Sqrt[a+b*x+c*x^2]/Sqrt[g+h*x+i*x^2]*Int[(a+b*x+c*x^2)^m*(d+e*x+f*Sqrt[a+b*x+c*x^2])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && EqQ[c*h-b*i,0] && ILtQ[m-1/2,0] && Not[GtQ[i/c,0]]


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m+1/2)*Sqrt[a+c*x^2]/Sqrt[g+i*x^2]*Int[(a+c*x^2)^m*(d+e*x+f*Sqrt[a+c*x^2])^n,x] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && ILtQ[m-1/2,0] && Not[GtQ[i/c,0]]


Int[w_^m_.*(u_+f_.*(j_.+k_.*Sqrt[v_]))^n_.,x_Symbol] :=
  Int[ExpandToSum[w,x]^m*(ExpandToSum[u+f*j,x]+f*k*Sqrt[ExpandToSum[v,x]])^n,x] /;
FreeQ[{f,j,k,m,n},x] && LinearQ[u,x] && QuadraticQ[{v,w},x] && 
  Not[LinearMatchQ[u,x] && QuadraticMatchQ[{v,w},x] && (EqQ[j,0] || EqQ[f,1])] && 
  EqQ[Coefficient[u,x,1]^2-Coefficient[v,x,2]*f^2*k^2,0]


Int[1/((a_+b_.*x_^n_.)*Sqrt[c_.*x_^2+d_.*(a_+b_.*x_^n_.)^p_.]),x_Symbol] :=
  1/a*Subst[Int[1/(1-c*x^2),x],x,x/Sqrt[c*x^2+d*(a+b*x^n)^(2/n)]] /;
FreeQ[{a,b,c,d,n},x] && EqQ[p,2/n]


Int[Sqrt[a_+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
  2*b^2*d*x^3/(3*(a+b*Sqrt[c+d*x^2])^(3/2)) + 2*a*x/Sqrt[a+b*Sqrt[c+d*x^2]] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2*c,0]


Int[Sqrt[a_.*x_^2+b_.*x_*Sqrt[c_+d_.*x_^2]]/(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[2]*b/a*Subst[Int[1/Sqrt[1+x^2/a],x],x,a*x+b*Sqrt[c+d*x^2]] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2*d,0] && EqQ[b^2*c+a,0]


Int[Sqrt[e_.*x_*(a_.*x_+b_.*Sqrt[c_+d_.*x_^2])]/(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Int[Sqrt[a*e*x^2+b*e*x*Sqrt[c+d*x^2]]/(x*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2*d,0] && EqQ[b^2*c*e+a,0]


Int[Sqrt[c_.*x_^2+d_.*Sqrt[a_+b_.*x_^4]]/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  d*Subst[Int[1/(1-2*c*x^2),x],x,x/Sqrt[c*x^2+d*Sqrt[a+b*x^4]]] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-b*d^2,0]


Int[(c_.+d_.*x_)^m_.*Sqrt[b_.*x_^2+Sqrt[a_+e_.*x_^4]]/Sqrt[a_+e_.*x_^4],x_Symbol] :=
  (1-I)/2*Int[(c+d*x)^m/Sqrt[Sqrt[a]-I*b*x^2],x] +
  (1+I)/2*Int[(c+d*x)^m/Sqrt[Sqrt[a]+I*b*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[e,b^2] && GtQ[a,0]


Int[1/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[b/a,3]},
  -q/((1+Sqrt[3])*d-c*q)*Int[1/Sqrt[a+b*x^3],x] + 
  d/((1+Sqrt[3])*d-c*q)*Int[(1+Sqrt[3]+q*x)/((c+d*x)*Sqrt[a+b*x^3]),x]] /;
FreeQ[{a,b,c,d},x] && PosQ[a] && PosQ[b]


Int[1/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[-b/a,3]},
  q/((1+Sqrt[3])*d+c*q)*Int[1/Sqrt[a+b*x^3],x] + 
  d/((1+Sqrt[3])*d+c*q)*Int[(1+Sqrt[3]-q*x)/((c+d*x)*Sqrt[a+b*x^3]),x]] /;
FreeQ[{a,b,c,d},x] && PosQ[a] && NegQ[b]


Int[1/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[-b/a,3]},
  q/((1-Sqrt[3])*d+c*q)*Int[1/Sqrt[a+b*x^3],x] + 
  d/((1-Sqrt[3])*d+c*q)*Int[(1-Sqrt[3]-q*x)/((c+d*x)*Sqrt[a+b*x^3]),x]] /;
FreeQ[{a,b,c,d},x] && NegQ[a] && PosQ[b]


Int[1/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[b/a,3]},
  -q/((1-Sqrt[3])*d-c*q)*Int[1/Sqrt[a+b*x^3],x] + 
  d/((1-Sqrt[3])*d-c*q)*Int[(1-Sqrt[3]+q*x)/((c+d*x)*Sqrt[a+b*x^3]),x]] /;
FreeQ[{a,b,c,d},x] && NegQ[a] && NegQ[b]


Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[b/a,3]},
  4*3^(1/4)*Sqrt[2-Sqrt[3]]*f*(1+q*x)*Sqrt[(1-q*x+q^2*x^2)/(1+Sqrt[3]+q*x)^2]/
    (q*Sqrt[a+b*x^3]*Sqrt[(1+q*x)/(1+Sqrt[3]+q*x)^2])*
    Subst[Int[1/(((1-Sqrt[3])*d-c*q+((1+Sqrt[3])*d-c*q)*x)*Sqrt[1-x^2]*Sqrt[7-4*Sqrt[3]+x^2]),x],x,(-1+Sqrt[3]-q*x)/(1+Sqrt[3]+q*x)] /;
 EqQ[(1+Sqrt[3])*f-e*q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[a] && PosQ[b]


Int[(e_.+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[b/a,3]},
  ((1+Sqrt[3])*f-e*q)/((1+Sqrt[3])*d-c*q)*Int[1/Sqrt[a+b*x^3],x] + 
  (d*e-c*f)/((1+Sqrt[3])*d-c*q)*Int[(1+Sqrt[3]+q*x)/((c+d*x)*Sqrt[a+b*x^3]),x] /;
 NeQ[(1+Sqrt[3])*f-e*q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[a] && PosQ[b]


Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[-b/a,3]},
  -4*3^(1/4)*Sqrt[2-Sqrt[3]]*f*(1-q*x)*Sqrt[(1+q*x+q^2*x^2)/(1+Sqrt[3]-q*x)^2]/
    (q*Sqrt[a+b*x^3]*Sqrt[(1-q*x)/(1+Sqrt[3]-q*x)^2])*
    Subst[Int[1/(((1-Sqrt[3])*d+c*q+((1+Sqrt[3])*d+c*q)*x)*Sqrt[1-x^2]*Sqrt[7-4*Sqrt[3]+x^2]),x],x,(-1+Sqrt[3]+q*x)/(1+Sqrt[3]-q*x)] /;
 EqQ[(1+Sqrt[3])*f+e*q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[a] && NegQ[b]


Int[(e_.+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[-b/a,3]},
  ((1+Sqrt[3])*f+e*q)/((1+Sqrt[3])*d+c*q)*Int[1/Sqrt[a+b*x^3],x] + 
  (d*e-c*f)/((1+Sqrt[3])*d+c*q)*Int[(1+Sqrt[3]-q*x)/((c+d*x)*Sqrt[a+b*x^3]),x] /;
 NeQ[(1+Sqrt[3])*f+e*q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[a] && NegQ[b]


Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[-b/a,3]},
  4*3^(1/4)*Sqrt[2+Sqrt[3]]*f*(1-q*x)*Sqrt[(1+q*x+q^2*x^2)/(1-Sqrt[3]-q*x)^2]/
    (q*Sqrt[a+b*x^3]*Sqrt[-(1-q*x)/(1-Sqrt[3]-q*x)^2])*
  Subst[Int[1/(((1+Sqrt[3])*d+c*q+((1-Sqrt[3])*d+c*q)*x)*Sqrt[1-x^2]*Sqrt[7+4*Sqrt[3]+x^2]),x],x,(1+Sqrt[3]-q*x)/(-1+Sqrt[3]+q*x)] /;
 EqQ[(1-Sqrt[3])*f+e*q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[a] && PosQ[b]


Int[(e_.+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[-b/a,3]},
  ((1-Sqrt[3])*f+e*q)/((1-Sqrt[3])*d+c*q)*Int[1/Sqrt[a+b*x^3],x] + 
  (d*e-c*f)/((1-Sqrt[3])*d+c*q)*Int[(1-Sqrt[3]-q*x)/((c+d*x)*Sqrt[a+b*x^3]),x] /;
 NeQ[(1-Sqrt[3])*f+e*q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[a] && PosQ[b]


Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[b/a,3]},
  -4*3^(1/4)*Sqrt[2+Sqrt[3]]*f*(1+q*x)*Sqrt[(1-q*x+q^2*x^2)/(1-Sqrt[3]+q*x)^2]/
   (q*Sqrt[a +b*x^3]*Sqrt[-(1+q*x)/(1-Sqrt[3]+q*x)^2])*
   Subst[Int[1/(((1+Sqrt[3])*d-c*q+((1-Sqrt[3])*d-c*q)*x)*Sqrt[1-x^2]*Sqrt[7+4*Sqrt[3]+x^2]),x],x,(1+Sqrt[3]+q*x)/(-1+Sqrt[3]-q*x)] /;
 EqQ[(1-Sqrt[3])*f-e*q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[a] && NegQ[b]


Int[(e_.+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
  With[{q=Rt[b/a,3]},
  ((1-Sqrt[3])*f-e*q)/((1-Sqrt[3])*d-c*q)*Int[1/Sqrt[a+b*x^3],x] + 
  (d*e-c*f)/((1-Sqrt[3])*d-c*q)*Int[(1-Sqrt[3]+q*x)/((c+d*x)*Sqrt[a+b*x^3]),x] /;
 NeQ[(1-Sqrt[3])*f-e*q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[a] && NegQ[b]


Int[x_^m_./(c_+d_.*x_^n_+e_.*Sqrt[a_+b_.*x_^n_]),x_Symbol] :=
  1/n*Subst[Int[x^((m+1)/n-1)/(c+d*x+e*Sqrt[a+b*x]),x],x,x^n] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[b*c-a*d,0] && IntegerQ[(m+1)/n]


Int[u_./(c_+d_.*x_^n_+e_.*Sqrt[a_+b_.*x_^n_]),x_Symbol] :=
  c*Int[u/(c^2-a*e^2+c*d*x^n),x] - a*e*Int[u/((c^2-a*e^2+c*d*x^n)*Sqrt[a+b*x^n]),x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[b*c-a*d,0]


Int[(A_+B_.*x_^n_)/(a_+b_.*x_^2+c_.*x_^n_+d_.*x_^n2_), x_Symbol] :=
  A^2*(n-1)*Subst[Int[1/(a+A^2*b*(n-1)^2*x^2),x],x,x/(A*(n-1)-B*x^n)] /;
FreeQ[{a,b,c,d,A,B,n},x] && EqQ[n2,2*n] && NeQ[n,2] && EqQ[a*B^2-A^2*d*(n-1)^2,0] && EqQ[B*c+2*A*d*(n-1),0]


Int[x_^m_.*(A_+B_.*x_^n_.)/(a_+b_.*x_^k_.+c_.*x_^n_.+d_.*x_^n2_), x_Symbol] :=
  A^2*(m-n+1)/(m+1)*Subst[Int[1/(a+A^2*b*(m-n+1)^2*x^2),x],x,x^(m+1)/(A*(m-n+1)+B*(m+1)*x^n)] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && EqQ[n2,2*n] && EqQ[k,2*(m+1)] && EqQ[a*B^2*(m+1)^2-A^2*d*(m-n+1)^2,0] && EqQ[B*c*(m+1)-2*A*d*(m-n+1),0]


Int[(a_.+b_.*x_^2+c_.*x_^4)/(d_+e_.*x_^2+f_.*x_^4+g_.*x_^6),x_Symbol] :=
  With[{q=Rt[(-a*c*f^2+12*a^2*g^2+f*(3*c^2*d-2*a*b*g))/(c*g*(3*c*d-a*f)),2],
        r=Rt[(a*c*f^2+4*g*(b*c*d+a^2*g)-f*(3*c^2*d+2*a*b*g))/(c*g*(3*c*d-a*f)),2]},
  c/(g*q)*ArcTan[(r+2*x)/q] - 
  c/(g*q)*ArcTan[(r-2*x)/q] - 
  c/(g*q)*ArcTan[(3*c*d-a*f)*x/(g*q*(b*c*d-2*a^2*g)*(b*c*d-a*b*f+4*a^2*g))*
    (b*c^2*d*f-a*b^2*f*g-2*a^2*c*f*g+6*a^2*b*g^2+c*(3*c^2*d*f-a*c*f^2-b*c*d*g+2*a^2*g^2)*x^2+c^2*g*(3*c*d-a*f)*x^4)]] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[9*c^3*d^2-c*(b^2+6*a*c)*d*f+a^2*c*f^2+2*a*b*(3*c*d+a*f)*g-12*a^3*g^2,0] && 
  EqQ[3*c^4*d^2*e-3*a^2*c^2*d*f*g+a^3*c*f^2*g+2*a^3*g^2*(b*f-6*a*g)-c^3*d*(2*b*d*f+a*e*f-12*a*d*g),0] && 
  NeQ[3*c*d-a*f,0] && NeQ[b*c*d-2*a^2*g,0] && NeQ[b*c*d-a*b*f+4*a^2*g,0] && 
  PosQ[(-a*c*f^2+12*a^2*g^2+f*(3*c^2*d-2*a*b*g))/(c*g*(3*c*d-a*f))]


Int[(a_.+c_.*x_^4)/(d_+e_.*x_^2+f_.*x_^4+g_.*x_^6),x_Symbol] :=
  With[{q=Rt[(-a*c*f^2+12*a^2*g^2+3*f*c^2*d)/(c*g*(3*c*d-a*f)),2],
        r=Rt[(a*c*f^2+4*a^2*g^2-3*c^2*d*f)/(c*g*(3*c*d-a*f)),2]},
  c/(g*q)*ArcTan[(r+2*x)/q] - 
  c/(g*q)*ArcTan[(r-2*x)/q] - 
  c/(g*q)*ArcTan[(c*(3*c*d-a*f)*x*(2*a^2*f*g-(3*c^2*d*f-a*c*f^2+2*a^2*g^2)*x^2-c*(3*c*d-a*f)*g*x^4))/(8*a^4*g^3*q)]] /;
FreeQ[{a,c,d,e,f,g},x] && EqQ[9*c^3*d^2-6*a*c^2*d*f+a^2*c*f^2-12*a^3*g^2,0] && 
  EqQ[3*c^4*d^2*e-3*a^2*c^2*d*f*g+a^3*c*f^2*g-12*a^4*g^3-a*c^3*d*(e*f-12*d*g),0] && 
  NeQ[3*c*d-a*f,0] && PosQ[(-a*c*f^2+12*a^2*g^2+3*c^2*d*f)/(c*g*(3*c*d-a*f))]


Int[u_.*Q6_^p_,x_Symbol] :=
  With[{a=Coeff[Q6,x,0],b=Coeff[Q6,x,2],c=Coeff[Q6,x,3],d=Coeff[Q6,x,4],e=Coeff[Q6,x,6]},
  1/(3^(3*p)*a^(2*p))*Int[ExpandIntegrand[u*
    (3*a+3*Rt[a,3]^2*Rt[c,3]*x+b*x^2)^p*
    (3*a-3*(-1)^(1/3)*Rt[a,3]^2*Rt[c,3]*x+b*x^2)^p*
    (3*a+3*(-1)^(2/3)*Rt[a,3]^2*Rt[c,3]*x+b*x^2)^p,x],x] /;
 EqQ[b^2-3*a*d,0] && EqQ[b^3-27*a^2*e,0]] /;
ILtQ[p,0] && PolyQ[Q6,x,6] && EqQ[Coeff[Q6,x,1],0] && EqQ[Coeff[Q6,x,5],0] && RationalFunctionQ[u,x]


If[ShowSteps,
Int[u_*v_^p_,x_Symbol] :=
  With[{m=Exponent[u,x],n=Exponent[v,x]},
  Module[{c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p)),w},
  w=Apart[u-c*x^(m-n)*((m-n+1)*v+(p+1)*x*D[v,x]),x];
  If[EqQ[w,0],
    ShowStep["
If p>1, 1<n<=m+1, and m+1-n*p<0, let c=pm/(qn*(m+1-n*p)), then if (\!\(\*SubscriptBox[\(P\), \(m\)]\)[x]-c*x^(m-n)*((m-n+1)*\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x]+(1-p)*x*D[\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x],x]))==0,",
	  "Int[\!\(\*SubscriptBox[\(P\), \(m\)]\)[x]/\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x]^p,x]", "c*x^(m-n+1)/\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x]^(p-1)",
      Hold[c*x^(m-n+1)*v^(p+1)]],
  ShowStep["If p>1, 1<n<=m+1, and m+1-n*p<0, let c=pm/(qn*(m+1-n*p)), then",
	"Int[\!\(\*SubscriptBox[\(P\), \(m\)]\)[x]/\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x]^p,x]",
	"c*x^(m-n+1)/\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x]^(p-1)+Int[(\!\(\*SubscriptBox[\(P\), \(m\)]\)[x]-c*x^(m-n)*((m-n+1)*\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x]+(1-p)*x*D[\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x],x]))/\!\(\*SubscriptBox[\(Q\), \(n\)]\)[x]^p,x]",
	Hold[c*x^(m-n+1)*v^(p+1) + Int[w*v^p,x]]]]] /;
 1<n<=m+1 && m+n*p<-1 && FalseQ[DerivativeDivides[v,u,x]]] /;
SimplifyFlag && RationalQ[p] && p<-1 && PolynomialQ[u,x] && PolynomialQ[v,x] && SumQ[v] && 
Not[MonomialQ[u,x] && BinomialQ[v,x]] && 
Not[EqQ[Coefficient[u,x,0],0] && EqQ[Coefficient[v,x,0],0]],
Int[u_*v_^p_,x_Symbol] :=
  With[{m=Exponent[u,x],n=Exponent[v,x]},
  Module[{c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p)),w},
  c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p));
  w=Apart[u-c*x^(m-n)*((m-n+1)*v+(p+1)*x*D[v,x]),x];
  If[EqQ[w,0],
    c*x^(m-n+1)*v^(p+1),
  c*x^(m-n+1)*v^(p+1) + Int[w*v^p,x]]] /;
 1<n<=m+1 && m+n*p<-1 && FalseQ[DerivativeDivides[v,u,x]]] /;
RationalQ[p] && p<-1 && PolynomialQ[u,x] && PolynomialQ[v,x] && SumQ[v] && 
Not[MonomialQ[u,x] && BinomialQ[v,x]] && 
Not[EqQ[Coefficient[u,x,0],0] && EqQ[Coefficient[v,x,0],0]]]
