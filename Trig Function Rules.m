(* ::Package:: *)

(* ::Section:: *)
(*Trig Function Rules*)


(* ::Subsection::Closed:: *)
(*1. trig(a+b x)^n*)


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


Int[Sqrt[sin[a_.+b_.*x_]],x_Symbol] :=
  -2*EllipticE[Pi/4-(a+b*x)/2,2]/b /;
FreeQ[{a,b},x]


Int[Sqrt[cos[a_.+b_.*x_]],x_Symbol] :=
  2*EllipticE[(a+b*x)/2,2]/b /;
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


Int[sin[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]*Sin[a+b*x]^(n-1)/(b*n) +
  (n-1)/n*Int[Sin[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && Not[OddQ[n]]


Int[cos[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]*Cos[a+b*x]^(n-1)/(b*n) + 
  (n-1)/n*Int[Cos[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && Not[OddQ[n]]


Int[1/Sqrt[sin[a_.+b_.*x_]],x_Symbol] :=
  -2*EllipticF[Pi/4-(a+b*x)/2,2]/b /;
FreeQ[{a,b},x]


Int[1/Sqrt[cos[a_.+b_.*x_]],x_Symbol] :=
  2*EllipticF[(a+b*x)/2,2]/b /;
FreeQ[{a,b},x]


Int[1/sin[a_.+b_.*x_]^2,x_Symbol] :=
  -Cot[a+b*x]/b /;
FreeQ[{a,b},x]


Int[1/cos[a_.+b_.*x_]^2,x_Symbol] :=
  Tan[a+b*x]/b /;
FreeQ[{a,b},x]


Int[sin[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]*Sin[a+b*x]^(n+1)/(b*(n+1)) + 
  (n+2)/(n+1)*Int[Sin[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1 && n!=-2


Int[cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sin[a+b*x]*Cos[a+b*x]^(n+1)/(b*(n+1)) + 
  (n+2)/((n+1))*Int[Cos[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1 && n!=-2


Int[sin[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]*Sin[a+b*x]^(n-1)/(b*(Sin[a+b*x]^2)^((n-1)/2))*
    Hypergeometric2F1[1/2,(1-n)/2,3/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,n},x] && Not[IntegerQ[n]] && RationalQ[n] && n>0


Int[cos[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]*Cos[a+b*x]^(n-1)/(b*(Cos[a+b*x]^2)^((n-1)/2))*
    Hypergeometric2F1[1/2,(1-n)/2,3/2,Sin[a+b*x]^2] /;
FreeQ[{a,b,n},x] && Not[IntegerQ[n]] && RationalQ[n] && n>0


Int[sin[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]*Sin[a+b*x]^(n+1)/(b*(Sin[a+b*x]^2)^((n+1)/2))*
    Hypergeometric2F1[1/2,(1-n)/2,3/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,n},x] && Not[IntegerQ[n]] && Not[RationalQ[n] && n>0]


Int[cos[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]*Cos[a+b*x]^(n+1)/(b*(Cos[a+b*x]^2)^((n+1)/2))*
    Hypergeometric2F1[1/2,(1-n)/2,3/2,Sin[a+b*x]^2] /;
FreeQ[{a,b,n},x] && Not[IntegerQ[n]] && Not[RationalQ[n] && n>0]


Int[tan[a_.+b_.*x_],x_Symbol] :=
  -Log[RemoveContent[Cos[a+b*x],x]]/b /;
FreeQ[{a,b},x]


Int[cot[a_.+b_.*x_],x_Symbol] :=
  Log[RemoveContent[Sin[a+b*x],x]]/b /;
FreeQ[{a,b},x]


Int[tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Tan[a+b*x]^(n-1)/(b*(n-1)) - 
  Int[Tan[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1


Int[cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cot[a+b*x]^(n-1)/(b*(n-1)) - 
  Int[Cot[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1


(* Int[1/tan[a_.+b_.*x_],x_Symbol] :=
  Log[RemoveContent[Sin[a+b*x],x]]/b /;
FreeQ[{a,b},x] *)


(* Int[1/cot[a_.+b_.*x_],x_Symbol] :=
  -Log[RemoveContent[Cos[a+b*x],x]]/b /;
FreeQ[{a,b},x] *)


Int[tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Tan[a+b*x]^(n+1)/(b*(n+1)) - 
  Int[Tan[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1


Int[cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cot[a+b*x]^(n+1)/(b*(n+1)) - 
  Int[Cot[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1


Int[Sqrt[tan[a_.+b_.*x_]],x_Symbol] :=
  1/2*Int[(1+Tan[a+b*x])/Sqrt[Tan[a+b*x]],x] - 1/2*Int[(1-Tan[a+b*x])/Sqrt[Tan[a+b*x]],x] /;
FreeQ[{a,b},x]


Int[Sqrt[cot[a_.+b_.*x_]],x_Symbol] :=
  1/2*Int[(1+Cot[a+b*x])/Sqrt[Cot[a+b*x]],x] - 1/2*Int[(1-Cot[a+b*x])/Sqrt[Cot[a+b*x]],x] /;
FreeQ[{a,b},x]


Int[1/Sqrt[tan[a_.+b_.*x_]],x_Symbol] :=
  1/2*Int[(1+Tan[a+b*x])/Sqrt[Tan[a+b*x]],x] + 1/2*Int[(1-Tan[a+b*x])/Sqrt[Tan[a+b*x]],x] /;
FreeQ[{a,b},x]


Int[1/Sqrt[cot[a_.+b_.*x_]],x_Symbol] :=
  1/2*Int[(1+Cot[a+b*x])/Sqrt[Cot[a+b*x]],x] + 1/2*Int[(1-Cot[a+b*x])/Sqrt[Cot[a+b*x]],x] /;
FreeQ[{a,b},x]


Int[tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Module[{k=Denominator[n]},
  k/b*Subst[Int[x^(k*(n+1)-1)/(1+x^(2*k)),x],x,Tan[a+b*x]^(1/k)]] /;
FreeQ[{a,b},x] && RationalQ[n] && -1<n<1


Int[cot[a_.+b_.*x_]^n_,x_Symbol] :=
  Module[{k=Denominator[n]},
  -k/b*Subst[Int[x^(k*(n+1)-1)/(1+x^(2*k)),x],x,Cot[a+b*x]^(1/k)]] /;
FreeQ[{a,b},x] && RationalQ[n] && -1<n<1


Int[tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Tan[a+b*x]^(n+1)/(b*(n+1))*Hypergeometric2F1[1,(n+1)/2,(n+3)/2,-Tan[a+b*x]^2] /;
FreeQ[{a,b,n},x] && Not[IntegerQ[n]]


Int[cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cot[a+b*x]^(n+1)/(b*(n+1))*Hypergeometric2F1[1,(n+1)/2,(n+3)/2,-Cot[a+b*x]^2] /;
FreeQ[{a,b,n},x] && Not[IntegerQ[n]]


Int[sec[a_.+b_.*x_],x_Symbol] :=
(* ArcCoth[Sin[a+b*x]]/b *)
  ArcTanh[Sin[a+b*x]]/b /;
FreeQ[{a,b},x]


Int[csc[a_.+b_.*x_],x_Symbol] :=
(* -ArcCoth[Cos[a+b*x]]/b /; *)
  -ArcTanh[Cos[a+b*x]]/b /;
FreeQ[{a,b},x]


Int[sec[a_.+b_.*x_]^2,x_Symbol] :=
  Tan[a+b*x]/b /;
FreeQ[{a,b},x]


Int[csc[a_.+b_.*x_]^2,x_Symbol] :=
  -Cot[a+b*x]/b /;
FreeQ[{a,b},x]


Int[sec[a_.+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[ExpandIntegrand[(1+x^2)^(n/2-1),x],x],x,Tan[a+b*x]] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && EvenQ[n]


Int[csc[a_.+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[ExpandIntegrand[(1+x^2)^(n/2-1),x],x],x,Cot[a+b*x]] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && EvenQ[n]


Int[sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]*Sec[a+b*x]^(n-1)/(b*(n-1)) + 
  (n-2)/(n-1)*Int[Sec[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && Not[EvenQ[n]]


Int[csc[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]*Csc[a+b*x]^(n-1)/(b*(n-1)) + 
  (n-2)/(n-1)*Int[Csc[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && Not[EvenQ[n]]


(* Int[1/sec[a_.+b_.*x_],x_Symbol] :=
  Sin[a+b*x]/b /;
FreeQ[{a,b},x] *)


(* Int[1/csc[a_.+b_.*x_],x_Symbol] :=
  -Cos[a+b*x]/b /;
FreeQ[{a,b},x] *)


Int[sec[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sin[a+b*x]*Sec[a+b*x]^(n+1)/(b*n) + 
  (n+1)/n*Int[Sec[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1


Int[csc[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]*Csc[a+b*x]^(n+1)/(b*n) + 
  (n+1)/n*Int[Csc[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1


Int[1/Sqrt[sec[a_.+b_.*x_]],x_Symbol] :=
  Sqrt[Cos[a+b*x]]*Sqrt[Sec[a+b*x]]*Int[Sqrt[Cos[a+b*x]],x] /;
FreeQ[{a,b},x]


Int[1/Sqrt[csc[a_.+b_.*x_]],x_Symbol] :=
  Sqrt[Csc[a+b*x]]*Sqrt[Sin[a+b*x]]*Int[Sqrt[Sin[a+b*x]],x] /;
FreeQ[{a,b},x]


Int[sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]^n*Sec[a+b*x]^n*Int[1/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && Not[IntegerQ[n]]


Int[csc[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^n*Csc[a+b*x]^n*Int[1/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && Not[IntegerQ[n]]


(* ::Subsection::Closed:: *)
(*2. (c trig(a+b x)^m)^n*)


Int[(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^n/Sin[a+b*x]^n*Int[Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n^2-1/4]


Int[(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^n/Cos[a+b*x]^n*Int[Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n^2-1/4]


Int[(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  c*(c*Sin[a+b*x])^(n-1)/Sin[a+b*x]^(n-1)*Int[Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && 0<n<1 && n!=1/2


Int[(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  c*(c*Cos[a+b*x])^(n-1)/Cos[a+b*x]^(n-1)*Int[Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && 0<n<1 && n!=1/2


Int[(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
(* -Cot[a+b*x]*(c*Sin[a+b*x])^n/(b*n) + *)
  -c*Cos[a+b*x]*(c*Sin[a+b*x])^(n-1)/(b*n) + 
  c^2*(n-1)/n*Int[(c*Sin[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
(* Tan[a+b*x]*(c*Cos[a+b*x])^n/(b*n) + *)
  c*Sin[a+b*x]*(c*Cos[a+b*x])^(n-1)/(b*n) + 
  c^2*(n-1)/n*Int[(c*Cos[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_.*sin[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  -Cot[a+b*x]*(c*Sin[a+b*x]^2)^n/(2*b*n) + 
  c*(2*n-1)/(2*n)*Int[(c*Sin[a+b*x]^2)^(n-1),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_.*cos[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  Tan[a+b*x]*(c*Cos[a+b*x]^2)^n/(2*b*n) + 
  c*(2*n-1)/(2*n)*Int[(c*Cos[a+b*x]^2)^(n-1),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^(n+1)/(c*Sin[a+b*x]^(n+1))*Int[Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -1<n<0 && n!=-1/2


Int[(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^(n+1)/(c*Cos[a+b*x]^(n+1))*Int[Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -1<n<0 && n!=-1/2


Int[(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]*(c*Sin[a+b*x])^(n+1)/(b*c*(n+1)) + 
  (n+2)/(c^2*(n+1))*Int[(c*Sin[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  -Sin[a+b*x]*(c*Cos[a+b*x])^(n+1)/(b*c*(n+1)) + 
  (n+2)/(c^2*(n+1))*Int[(c*Cos[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_.*sin[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  Cot[a+b*x]*(c*Sin[a+b*x]^2)^(n+1)/(b*c*(2*n+1)) + 
  2*(n+1)/(c*(2*n+1))*Int[(c*Sin[a+b*x]^2)^(n+1),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_.*cos[a_.+b_.*x_]^2)^n_,x_Symbol] :=
  -Tan[a+b*x]*(c*Cos[a+b*x]^2)^(n+1)/(b*c*(2*n+1)) + 
  2*(n+1)/(c*(2*n+1))*Int[(c*Cos[a+b*x]^2)^(n+1),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^(n+1)/(c*Sin[a+b*x]^(n+1))*Int[Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n]]


Int[(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^(n+1)/(c*Cos[a+b*x]^(n+1))*Int[Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n]]


Int[(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  c*(c*Tan[a+b*x])^(n-1)/(b*(n-1)) - 
  c^2*Int[(c*Tan[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*(c*Cot[a+b*x])^(n-1)/(b*(n-1)) - 
  c^2*Int[(c*Cot[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Tan[a+b*x])^(n+1)/(b*c*(n+1)) - 
  1/c^2*Int[(c*Tan[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Cot[a+b*x])^(n+1)/(b*c*(n+1)) - 
  1/c^2*Int[(c*Cot[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*c/b*Subst[Int[x^(k*(n+1)-1)/(c^2+x^(2*k)),x],x,(c*Tan[a+b*x])^(1/k)]] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -1<n<1


Int[(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  Module[{k=Denominator[n]},
  -k*c/b*Subst[Int[x^(k*(n+1)-1)/(c^2+x^(2*k)),x],x,(c*Cot[a+b*x])^(1/k)]] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -1<n<1


Int[(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Tan[a+b*x])^(n+1)/(b*c*(n+1))*Hypergeometric2F1[1,(n+1)/2,(n+3)/2,-Tan[a+b*x]^2] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n]]


Int[(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  -(c*Cot[a+b*x])^(n+1)/(b*c*(n+1))*Hypergeometric2F1[1,(n+1)/2,(n+3)/2,-Cot[a+b*x]^2] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n]]


Int[(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c*Sin[a+b*x]*(c*Sec[a+b*x])^(n-1)/(b*(n-1)) + 
  c^2*(n-2)/(n-1)*Int[(c*Sec[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*Cos[a+b*x]*(c*Csc[a+b*x])^(n-1)/(b*(n-1)) + 
  c^2*(n-2)/(n-1)*Int[(c*Csc[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1


Int[(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  -Sin[a+b*x]*(c*Sec[a+b*x])^(n+1)/(b*c*n) + 
  (n+1)/(c^2*n)*Int[(c*Sec[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]*(c*Csc[a+b*x])^(n+1)/(b*c*n) + 
  (n+1)/(c^2*n)*Int[(c*Csc[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]^n*(c*Sec[a+b*x])^n*Int[1/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && IntegerQ[n-1/2]


Int[(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  Sin[a+b*x]^n*(c*Csc[a+b*x])^n*Int[1/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && IntegerQ[n-1/2]


Int[(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  1/c*Cos[a+b*x]^(n+1)*(c*Sec[a+b*x])^(n+1)*Int[1/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<0


Int[(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  1/c*Sin[a+b*x]^(n+1)*(c*Csc[a+b*x])^(n+1)*Int[1/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<0


Int[(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c*Cos[a+b*x]^(n-1)*(c*Sec[a+b*x])^(n-1)*Int[1/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n]]


Int[(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  c*Sin[a+b*x]^(n-1)*(c*Csc[a+b*x])^(n-1)*Int[1/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n]]


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
(*3. trig(a+b x)^m trig(a+b x)^n*)


Int[sin[a_.+b_.*x_]^m_.*cos[a_.+b_.*x_],x_Symbol] :=
  Sin[a+b*x]^(m+1)/(b*(m+1)) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]


Int[sin[a_.+b_.*x_]*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]^(n+1)/(b*(n+1)) /;
FreeQ[{a,b,n},x] && NonzeroQ[n+1]


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n+1)/(b*(m+1)) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+2] && NonzeroQ[m+1]


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[x^m*(1-x^2)^((n-1)/2),x],x,Sin[a+b*x]] /;
FreeQ[{a,b,m},x] && OddQ[n] && Not[OddQ[m] && 0<m<n]


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[x^n*(1-x^2)^((m-1)/2),x],x,Cos[a+b*x]] /;
FreeQ[{a,b,n},x] && OddQ[m] && Not[OddQ[n] && 0<n<=m]


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sin[a+b*x]^(m-1)*Cos[a+b*x]^(n+1)/(b*(n+1)) + 
  (m-1)/(n+1)*Int[Sin[a+b*x]^(m-2)*Cos[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m>1 && n<-1


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n-1)/(b*(m+1)) + 
  (n-1)/(m+1)*Int[Sin[a+b*x]^(m+2)*Cos[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m<-1 && n>1


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sin[a+b*x]^(m-1)*Cos[a+b*x]^(n+1)/(b*(m+n)) + 
  (m-1)/(m+n)*Int[Sin[a+b*x]^(m-2)*Cos[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n]


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n-1)/(b*(m+n)) + 
  (n-1)/(m+n)*Int[Sin[a+b*x]^m*Cos[a+b*x]^(n-2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n]


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n+1)/(b*(m+1)) + 
  (m+n+2)/(m+1)*Int[Sin[a+b*x]^(m+2)*Cos[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+2]


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n+1)/(b*(n+1)) + 
  (m+n+2)/(n+1)*Int[Sin[a+b*x]^m*Cos[a+b*x]^(n+2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+2]


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  Module[{k=Denominator[m]},
  k*c*d/b*Subst[Int[x^(k*(m+1)-1)/(c^2+d^2*x^(2*k)),x],x,(c*Sin[a+b*x])^(1/k)/(d*Cos[a+b*x])^(1/k)]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && RationalQ[m] && 0<m<1


Int[(c_.*sin[a_.+b_.*x_])^m_*(d_.*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  Module[{k=Denominator[m]},
  -k*c*d/b*Subst[Int[x^(k*(n+1)-1)/(d^2+c^2*x^(2*k)),x],x,(d*Cos[a+b*x])^(1/k)/(c*Sin[a+b*x])^(1/k)]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m+n] && RationalQ[m] && -1<m<0


Int[sin[a_.+b_.*x_]^m_*cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n+1)/(b*(n+1)*(Sin[a+b*x]^2)^((m+1)/2))*
    Hypergeometric2F1[-(m-1)/2,(n+1)/2,(n+3)/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]


Int[sin[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol]:=
  -Sin[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*m) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-1]


Int[cos[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*m) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-1]


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


Int[sin[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*m) - 
  (n+1)/m*Int[Sin[a+b*x]^(m-2)*Tan[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m>1 && n<-1


Int[cos[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*m) - 
  (n+1)/m*Int[Cos[a+b*x]^(m-2)*Cot[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m>1 && n<-1


Int[sin[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_.,x_Symbol]:=
  -Sin[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*m) + 
  (m+n-1)/m*Int[Sin[a+b*x]^(m-2)*Tan[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1]


Int[cos[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  Cos[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*m) + 
  (m+n-1)/m*Int[Cos[a+b*x]^(m-2)*Cot[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1]


Int[tan[a_.+b_.*x_]^n_/sin[a_.+b_.*x_]^2,x_Symbol] :=
  Tan[a+b*x]^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,n},x] && NonzeroQ[n-1]


Int[cot[a_.+b_.*x_]^n_/cos[a_.+b_.*x_]^2,x_Symbol] :=
  -Cot[a+b*x]^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,n},x] && NonzeroQ[n-1]


Int[sin[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^(m+2)*Tan[a+b*x]^(n-1)/(b*(n-1)) - 
  (m+2)/(n-1)*Int[Sin[a+b*x]^(m+2)*Tan[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m<-1 && m!=-2 && n>1


Int[cos[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]^(m+2)*Cot[a+b*x]^(n-1)/(b*(n-1)) - 
  (m+2)/(n-1)*Int[Cos[a+b*x]^(m+2)*Cot[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m<-1 && m!=-2 && n>1


Int[sin[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_.,x_Symbol]:=
  Sin[a+b*x]^(m+2)*Tan[a+b*x]^(n-1)/(b*(m+n+1)) + 
  (m+2)/(m+n+1)*Int[Sin[a+b*x]^(m+2)*Tan[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && m!=-2 && NonzeroQ[m+n+1]


Int[cos[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  -Cos[a+b*x]^(m+2)*Cot[a+b*x]^(n-1)/(b*(m+n+1)) + 
  (m+2)/(m+n+1)*Int[Cos[a+b*x]^(m+2)*Cot[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && m!=-2 && NonzeroQ[m+n+1]


Int[sin[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*(n-1)) - 
  (m+n-1)/(n-1)*Int[Sin[a+b*x]^m*Tan[a+b*x]^(n-2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1]


Int[cos[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*(n-1)) - 
  (m+n-1)/(n-1)*Int[Cos[a+b*x]^m*Cot[a+b*x]^(n-2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1]


Int[sin[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_,x_Symbol]:=
  Sin[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*(m+n+1)) - 
  (n+1)/(m+n+1)*Int[Sin[a+b*x]^m*Tan[a+b*x]^(n+2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1]


Int[cos[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Cos[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*(m+n+1)) - 
  (n+1)/(m+n+1)*Int[Cos[a+b*x]^m*Cot[a+b*x]^(n+2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1]


Int[sin[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]^n*Tan[a+b*x]^n/Sin[a+b*x]^n*Int[Sin[a+b*x]^(m+n)/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[n]]


Int[cos[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^n*Cot[a+b*x]^n/Cos[a+b*x]^n*Int[Cos[a+b*x]^(m+n)/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[n]]


Int[sin[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^n*Cot[a+b*x]^n/Cos[a+b*x]^n*Int[Sin[a+b*x]^(m-n)*Cos[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x]


Int[cos[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]^n*Tan[a+b*x]^n/Sin[a+b*x]^n*Int[Sin[a+b*x]^n*Cos[a+b*x]^(m-n),x] /;
FreeQ[{a,b,m,n},x]


Int[sin[a_.+b_.*x_]*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Sec[a+b*x]^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,n},x] && NonzeroQ[n-1]


Int[cos[a_.+b_.*x_]*csc[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,n},x] && NonzeroQ[n-1]


Int[sin[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]^n*Sec[a+b*x]^n*Int[Sin[a+b*x]^m/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[n]]


Int[cos[a_.+b_.*x_]^m_.*csc[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^n*Csc[a+b*x]^n*Int[Cos[a+b*x]^m/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[n]]


Int[sin[a_.+b_.*x_]^m_*csc[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^n*Csc[a+b*x]^n*Int[Sin[a+b*x]^(m-n),x] /;
FreeQ[{a,b,m,n},x]


Int[cos[a_.+b_.*x_]^m_*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]^n*Sec[a+b*x]^n*Int[Cos[a+b*x]^(m-n),x] /;
FreeQ[{a,b,m,n},x]


Int[csc[a_.+b_.*x_]^m_*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n-1)/(b*(n-1)) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-2] && NonzeroQ[n-1]


(* Int[csc[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_.,x_Symbol] :=
  -1/b*Subst[Int[1/(x^n*(1-x^2)^((m+1)/2)),x],x,Cos[a+b*x]] /;
FreeQ[{a,b},x] && OddQ[m] && IntegerQ[n] *)


(* Int[csc[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[1/(x^m*(1-x^2)^((n+1)/2)),x],x,Sin[a+b*x]] /;
FreeQ[{a,b},x] && OddQ[n] && IntegerQ[m] *)


Int[csc[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[(1+x^2)^((m+n)/2-1)/x^m,x],x,Tan[a+b*x]] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && EvenQ[m+n]


Int[csc[a_.+b_.*x_]^m_*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n+1)/(b*(m-1)) + 
  (n+1)/(m-1)*Int[Csc[a+b*x]^(m-2)*Sec[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m>1 && n<-1


Int[csc[a_.+b_.*x_]^m_*sec[a_.+b_.*x_]^n_.,x_Symbol] :=
  -Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n-1)/(b*(m-1)) + 
  (m+n-2)/(m-1)*Int[Csc[a+b*x]^(m-2)*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-2] && Not[EvenQ[m] && OddQ[n] && n>1]


Int[csc[a_.+b_.*x_]^m_*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Csc[a+b*x]^(m+1)*Sec[a+b*x]^(n-1)/(b*(n-1)) + 
  (m+1)/(n-1)*Int[Csc[a+b*x]^(m+2)*Sec[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m<-1 && n>1


Int[csc[a_.+b_.*x_]^m_*sec[a_.+b_.*x_]^n_.,x_Symbol] :=
  Csc[a+b*x]^(m+1)*Sec[a+b*x]^(n-1)/(b*(m+n)) + 
  (m+1)/(m+n)*Int[Csc[a+b*x]^(m+2)*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n]


Int[csc[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n-1)/(b*(n-1)) + 
  (m+n-2)/(n-1)*Int[Csc[a+b*x]^m*Sec[a+b*x]^(n-2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-2]


Int[csc[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n+1)/(b*(m+n)) + 
  (n+1)/(m+n)*Int[Csc[a+b*x]^m*Sec[a+b*x]^(n+2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n]


Int[csc[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_.,x_Symbol] :=
  Csc[a+b*x]^m*Sec[a+b*x]^n/Tan[a+b*x]^n*Int[Tan[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && (Not[IntegerQ[m]] || Not[IntegerQ[n]]) && ZeroQ[m+n]


Int[csc[a_.+b_.*x_]^m_.*sec[a_.+b_.*x_]^n_.,x_Symbol] :=
  Sin[a+b*x]^m*Cos[a+b*x]^n*Csc[a+b*x]^m*Sec[a+b*x]^n*Int[1/(Sin[a+b*x]^m*Cos[a+b*x]^n),x] /;
FreeQ[{a,b,m,n},x] && (Not[IntegerQ[m]] || Not[IntegerQ[n]]) && NonzeroQ[m+n]


Int[sec[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_],x_Symbol] :=
  Sec[a+b*x]^m/(b*m) /;
FreeQ[{a,b,m},x]


Int[csc[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_],x_Symbol] :=
  -Csc[a+b*x]^m/(b*m) /;
FreeQ[{a,b,m},x]


Int[sec[a_.+b_.*x_]^2*tan[a_.+b_.*x_]^n_.,x_Symbol] :=
  Tan[a+b*x]^(n+1)/(b*(n+1)) /;
FreeQ[{a,b,n},x] && NonzeroQ[n+1]


Int[csc[a_.+b_.*x_]^2*cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  -Cot[a+b*x]^(n+1)/(b*(n+1)) /;
FreeQ[{a,b,n},x] && NonzeroQ[n+1]


Int[sec[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sec[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*m) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+1]


Int[csc[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  Csc[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*m) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+1]


Int[sec[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[x^n*(1+x^2)^((m-2)/2),x],x,Tan[a+b*x]] /;
FreeQ[{a,b,n},x] && EvenQ[m] && Not[OddQ[n] && 0<n<m-1]


Int[csc[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  -1/b*Subst[Int[x^n*(1+x^2)^((m-2)/2),x],x,Cot[a+b*x]] /;
FreeQ[{a,b,n},x] && EvenQ[m] && Not[OddQ[n] && 0<n<m-1]


Int[sec[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_.,x_Symbol] :=
  1/b*Subst[Int[x^(m-1)*(-1+x^2)^((n-1)/2),x],x,Sec[a+b*x]] /;
FreeQ[{a,b,m},x] && OddQ[n] && Not[EvenQ[m] && 0<m<=n+1]


Int[csc[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  -1/b*Subst[Int[x^(m-1)*(-1+x^2)^((n-1)/2),x],x,Csc[a+b*x]] /;
FreeQ[{a,b,m},x] && OddQ[n] && Not[EvenQ[m] && 0<m<=n+1]


Int[sec[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Sec[a+b*x]^(m-2)*Tan[a+b*x]^(n+1)/(b*(n+1)) -
  (m-2)/(n+1)*Int[Sec[a+b*x]^(m-2)*Tan[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m>1 && n<-1 && Not[EvenQ[m]]


Int[csc[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^(m-2)*Cot[a+b*x]^(n+1)/(b*(n+1)) -
  (m-2)/(n+1)*Int[Csc[a+b*x]^(m-2)*Cot[a+b*x]^(n+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m>1 && n<-1 && Not[EvenQ[m]]


Int[sec[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Sec[a+b*x]^(m-2)*Tan[a+b*x]^(n+1)/(b*(m+n-1)) +
  (m-2)/(m+n-1)*Int[Sec[a+b*x]^(m-2)*Tan[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1]


Int[csc[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^(m-2)*Cot[a+b*x]^(n+1)/(b*(m+n-1)) +
  (m-2)/(m+n-1)*Int[Csc[a+b*x]^(m-2)*Cot[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1]


Int[sec[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Sec[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*m) -
  (n-1)/m*Int[Sec[a+b*x]^(m+2)*Tan[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m<-1 && n>1


Int[csc[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*m) -
  (n-1)/m*Int[Csc[a+b*x]^(m+2)*Cot[a+b*x]^(n-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m<-1 && n>1


Int[sec[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sec[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*m) + 
  (m+n+1)/m*Int[Sec[a+b*x]^(m+2)*Tan[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+1]


Int[csc[a_.+b_.*x_]^m_*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*m) - 
  (m+n+1)/m*Int[Csc[a+b*x]^(m+2)*Cot[a+b*x]^n,x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+1]


Int[sec[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Sec[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*(m+n-1)) -
  (n-1)/(m+n-1)*Int[Sec[a+b*x]^m*Tan[a+b*x]^(n-2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1]


Int[csc[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*(m+n-1)) -
  (n-1)/(m+n-1)*Int[Csc[a+b*x]^m*Cot[a+b*x]^(n-2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1]


Int[sec[a_.+b_.*x_]^m_*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Sec[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*(n+1)) -
  (m+n+1)/(n+1)*Int[Sec[a+b*x]^m*Tan[a+b*x]^(n+2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1]


Int[csc[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -Csc[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*(n+1)) -
  (m+n+1)/(n+1)*Int[Csc[a+b*x]^m*Cot[a+b*x]^(n+2),x] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1]


Int[sec[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Csc[a+b*x]^n*Tan[a+b*x]^n/Sec[a+b*x]^n*Int[Sec[a+b*x]^(m+n)/Csc[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[n]]


Int[csc[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  Sec[a+b*x]^n*Cot[a+b*x]^n/Csc[a+b*x]^n*Int[Csc[a+b*x]^(m+n)/Sec[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x] && Not[IntegerQ[n]]


Int[sec[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  Sec[a+b*x]^n*Cot[a+b*x]^n/Csc[a+b*x]^n*Int[Csc[a+b*x]^n*Sec[a+b*x]^(m-n),x] /;
FreeQ[{a,b,m,n},x]


Int[csc[a_.+b_.*x_]^m_.*tan[a_.+b_.*x_]^n_,x_Symbol] :=
  Csc[a+b*x]^n*Tan[a+b*x]^n/Sec[a+b*x]^n*Int[Csc[a+b*x]^(m-n)*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,m,n},x]


Int[tan[a_.+b_.*x_]^m_.*cot[a_.+b_.*x_]^n_,x_Symbol] :=
  Tan[a+b*x]^n*Cot[a+b*x]^n*Int[Tan[a+b*x]^(m-n),x] /;
FreeQ[{a,b,m,n},x]


Int[sin[a_.+b_.*x_]*sin[c_.+d_.*x_],x_Symbol] :=
  Sin[a-c+(b-d)*x]/(2*(b-d)) - Sin[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b^2-d^2]


Int[cos[a_.+b_.*x_]*cos[c_.+d_.*x_],x_Symbol] :=
  Sin[a-c+(b-d)*x]/(2*(b-d)) + Sin[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b^2-d^2]


Int[sin[a_.+b_.*x_]*cos[c_.+d_.*x_],x_Symbol] :=
  -Cos[a-c+(b-d)*x]/(2*(b-d)) - Cos[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b^2-d^2]


Int[sin[c_.+d_.*x_]^2*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  1/2*Int[Sin[a+b*x]^n,x] - 
  1/2*Int[Cos[a+b*x]*Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && PositiveIntegerQ[n/2]


Int[sin[c_.+d_.*x_]^m_.*sin[a_.+b_.*x_]^n_.,x_Symbol] :=
  2^n*Int[Cos[c+d*x]^n*Sin[c+d*x]^(m+n),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && IntegerQ[n]


Int[sin[c_.+d_.*x_]*sin[a_.+b_.*x_]^n_.,x_Symbol] :=
  -2*Cos[c+d*x]*Sin[a+b*x]^n/(b*(2*n+1)) + 
  2*n/(2*n+1)*Int[Cos[c+d*x]*Sin[a+b*x]^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && FractionQ[n] && n>0


Int[sin[c_.+d_.*x_]/Sqrt[sin[a_.+b_.*x_]],x_Symbol] :=
  -ArcSin[Cos[c+d*x]-Sin[c+d*x]]/b - Log[Cos[c+d*x]+Sin[c+d*x]+Sqrt[Sin[a+b*x]]]/b /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2]


Int[sin[c_.+d_.*x_]/sin[a_.+b_.*x_]^(3/2),x_Symbol] :=
  2*Sin[c+d*x]/(b*Sqrt[Sin[a+b*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2]


Int[sin[c_.+d_.*x_]*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sin[c+d*x]*Sin[a+b*x]^(n+1)/(b*(n+1)) + 
  (2*n+3)/(2*(n+1))*Int[Cos[c+d*x]*Sin[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && FractionQ[n] && n<-1 && n!=-3/2


Int[sin[c_.+d_.*x_]^2*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  1/2*Int[Sin[a+b*x]^n,x] - 
  1/2*Int[Cos[a+b*x]*Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && Not[IntegerQ[n]]


Int[sin[c_.+d_.*x_]^m_.*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^n/(Cos[c+d*x]^n*Sin[c+d*x]^n)*Int[Cos[c+d*x]^n*Sin[c+d*x]^(m+n),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && Not[IntegerQ[n]]


Int[cos[c_.+d_.*x_]^2*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  1/2*Int[Sin[a+b*x]^n,x] + 
  1/2*Int[Cos[a+b*x]*Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && PositiveIntegerQ[n/2]


Int[cos[c_.+d_.*x_]^m_.*sin[a_.+b_.*x_]^n_.,x_Symbol] :=
  2^n*Int[Cos[c+d*x]^(m+n)*Sin[c+d*x]^n,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && IntegerQ[n]


Int[cos[c_.+d_.*x_]*sin[a_.+b_.*x_]^n_.,x_Symbol] :=
  2*Sin[c+d*x]*Sin[a+b*x]^n/(b*(2*n+1)) + 
  2*n/(2*n+1)*Int[Sin[c+d*x]*Sin[a+b*x]^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && FractionQ[n] && n>0


Int[cos[c_.+d_.*x_]/Sqrt[sin[a_.+b_.*x_]],x_Symbol] :=
  -ArcSin[Cos[c+d*x]-Sin[c+d*x]]/b + Log[Cos[c+d*x]+Sin[c+d*x]+Sqrt[Sin[a+b*x]]]/b /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2]


Int[cos[c_.+d_.*x_]/sin[a_.+b_.*x_]^(3/2),x_Symbol] :=
  -2*Cos[c+d*x]/(b*Sqrt[Sin[a+b*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2]


Int[cos[c_.+d_.*x_]*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[c+d*x]*Sin[a+b*x]^(n+1)/(b*(n+1)) + 
  (2*n+3)/(2*(n+1))*Int[Sin[c+d*x]*Sin[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && FractionQ[n] && n<-1 && n!=-3/2


Int[cos[c_.+d_.*x_]^2*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  1/2*Int[Sin[a+b*x]^n,x] + 
  1/2*Int[Cos[a+b*x]*Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && Not[IntegerQ[n]]


Int[cos[c_.+d_.*x_]^m_.*sin[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^n/(Cos[c+d*x]^n*Sin[c+d*x]^n)*Int[Cos[c+d*x]^(m+n)*Sin[c+d*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && Not[IntegerQ[n]]


Int[cos[c_.+d_.*x_]^2*sin[c_.+d_.*x_]^2*sin[a_.+b_.*x_]^p_,x_Symbol] :=
  1/4*Int[Sin[a+b*x]^p,x] + 
  1/4*Int[Cos[a+b*x]^2*Sin[a+b*x]^p,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && PositiveIntegerQ[p/2]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*sin[a_.+b_.*x_]^p_.,x_Symbol] :=
  2^n*Int[Cos[c+d*x]^(m+p)*Sin[c+d*x]^(n+p),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && IntegerQ[p]


Int[cos[c_.+d_.*x_]^2*sin[c_.+d_.*x_]^2*sin[a_.+b_.*x_]^p_,x_Symbol] :=
  1/4*Int[Sin[a+b*x]^p,x] + 
  1/4*Int[Cos[a+b*x]^2*Sin[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && Not[IntegerQ[p]]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*sin[a_.+b_.*x_]^p_,x_Symbol] :=
  Sin[a+b*x]^n/(Cos[c+d*x]^p*Sin[c+d*x]^p)*Int[Cos[c+d*x]^(m+p)*Sin[c+d*x]^(n+p),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[b*c-a*d] && ZeroQ[b/d-2] && Not[IntegerQ[p]]


(* ::Subsection::Closed:: *)
(*4. trig(a+b x)^m (c trig(a+b x))^n*)


(* Int[sin[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^n*Int[Sin[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && (IntegerQ[n] || PositiveQ[c]) *)


(* Int[cos[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^n*Int[Cos[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && (IntegerQ[n] || PositiveQ[c]) *)


Int[sin[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
  1/c^m*Int[(c*Sin[a+b*x])^(m+n),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[cos[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  1/c^m*Int[(c*Cos[a+b*x])^(m+n),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[sin[a_.+b_.*x_]^m_*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n-1/2)*Sqrt[c*Sin[a+b*x]]/Sqrt[Sin[a+b*x]]*Int[Sin[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[cos[a_.+b_.*x_]^m_*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n-1/2)*Sqrt[c*Cos[a+b*x]]/Sqrt[Cos[a+b*x]]*Int[Cos[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sin[a_.+b_.*x_]^m_*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n+1/2)*Sqrt[Sin[a+b*x]]/Sqrt[c*Sin[a+b*x]]*Int[Sin[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[cos[a_.+b_.*x_]^m_*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n+1/2)*Sqrt[Cos[a+b*x]]/Sqrt[c*Cos[a+b*x]]*Int[Cos[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sin[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^n/Sin[a+b*x]^n*Int[Sin[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[cos[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^n/Cos[a+b*x]^n*Int[Cos[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[cos[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^n/Sin[a+b*x]^n*Int[Cos[a+b*x]^m*Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[sin[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^n/Cos[a+b*x]^n*Int[Cos[a+b*x]^n*Sin[a+b*x]^m,x] /;
FreeQ[{a,b,c,m,n},x]


Int[tan[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sin[a+b*x])^n/Sin[a+b*x]^n*Int[Tan[a+b*x]^m*Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[cot[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cos[a+b*x])^n/Cos[a+b*x]^n*Int[Cot[a+b*x]^m*Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[cot[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  Csc[a+b*x]^n*(c*Sin[a+b*x])^n*Int[Cot[a+b*x]^m/Csc[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[tan[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  Sec[a+b*x]^n*(c*Cos[a+b*x])^n*Int[Tan[a+b*x]^m/Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[sec[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  Csc[a+b*x]^n*(c*Sin[a+b*x])^n*Int[Sec[a+b*x]^m/Csc[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[csc[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  Sec[a+b*x]^n*(c*Cos[a+b*x])^n*Int[Csc[a+b*x]^m/Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[csc[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^m*Int[(c*Sin[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[sec[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^m*Int[(c*Cos[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[csc[a_.+b_.*x_]^m_*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n-1/2)*Sqrt[Csc[a+b*x]]*Sqrt[c*Sin[a+b*x]]*Int[Csc[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sec[a_.+b_.*x_]^m_*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n-1/2)*Sqrt[Sec[a+b*x]]*Sqrt[c*Cos[a+b*x]]*Int[Sec[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[csc[a_.+b_.*x_]^m_*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n+1/2)/(Sqrt[Csc[a+b*x]]*Sqrt[c*Sin[a+b*x]])*Int[Csc[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sec[a_.+b_.*x_]^m_*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n+1/2)/(Sqrt[Sec[a+b*x]]*Sqrt[c*Cos[a+b*x]])*Int[Sec[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[csc[a_.+b_.*x_]^m_.*(c_*sin[a_.+b_.*x_])^n_,x_Symbol] :=
  Csc[a+b*x]^n*(c*Sin[a+b*x])^n*Int[Csc[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[sec[a_.+b_.*x_]^m_.*(c_*cos[a_.+b_.*x_])^n_,x_Symbol] :=
  Sec[a+b*x]^n*(c*Cos[a+b*x])^n*Int[Sec[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[sin[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Tan[a+b*x])^n/Tan[a+b*x]^n*Int[Sin[a+b*x]^m*Tan[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[cos[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cot[a+b*x])^n/Cot[a+b*x]^n*Int[Cos[a+b*x]^m*Cot[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[cos[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  Cot[a+b*x]^n*(c*Tan[a+b*x])^n*Int[Cos[a+b*x]^m/Cot[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[sin[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  Tan[a+b*x]^n*(c*Cot[a+b*x])^n*Int[Sin[a+b*x]^m/Tan[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


(* Int[tan[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^n*Int[Tan[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && (IntegerQ[n] || PositiveQ[c]) *)


(* Int[cot[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^n*Int[Cot[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && (IntegerQ[n] || PositiveQ[c]) *)


Int[tan[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
  1/c^m*Int[(c*Tan[a+b*x])^(m+n),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[cot[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_.,x_Symbol] :=
  1/c^m*Int[(c*Cot[a+b*x])^(m+n),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[tan[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Tan[a+b*x])^n/Tan[a+b*x]^n*Int[Tan[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]]


Int[cot[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cot[a+b*x])^n/Cot[a+b*x]^n*Int[Cot[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]]


Int[cot[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^m*Int[(c*Tan[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[tan[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^m*Int[(c*Cot[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[cot[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  Cot[a+b*x]^n*(c*Tan[a+b*x])^n*Int[Cot[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]]


Int[tan[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  Tan[a+b*x]^n*(c*Cot[a+b*x])^n*Int[Tan[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]]


Int[sec[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Tan[a+b*x])^n/Tan[a+b*x]^n*Int[Sec[a+b*x]^m*Tan[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[csc[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Cot[a+b*x])^n/Cot[a+b*x]^n*Int[Csc[a+b*x]^m*Cot[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[csc[a_.+b_.*x_]^m_.*(c_*tan[a_.+b_.*x_])^n_,x_Symbol] :=
  Cot[a+b*x]^n*(c*Tan[a+b*x])^n*Int[Csc[a+b*x]^m/Cot[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[sec[a_.+b_.*x_]^m_.*(c_*cot[a_.+b_.*x_])^n_,x_Symbol] :=
  Tan[a+b*x]^n*(c*Cot[a+b*x])^n*Int[Sec[a+b*x]^m/Tan[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[sin[a_.+b_.*x_]^m_.*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]^n*(c*Sec[a+b*x])^n*Int[Sin[a+b*x]^m/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[cos[a_.+b_.*x_]^m_.*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  Sin[a+b*x]^n*(c*Csc[a+b*x])^n*Int[Cos[a+b*x]^m/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[cos[a_.+b_.*x_]^m_.*(c_*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^m*Int[(c*Sec[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[sin[a_.+b_.*x_]^m_.*(c_*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^m*Int[(c*Csc[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[cos[a_.+b_.*x_]^m_*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n-1/2)*Sqrt[Cos[a+b*x]]*Sqrt[c*Sec[a+b*x]]*Int[Cos[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sin[a_.+b_.*x_]^m_*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n-1/2)*Sqrt[Sin[a+b*x]]*Sqrt[c*Csc[a+b*x]]*Int[Sin[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[cos[a_.+b_.*x_]^m_*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n+1/2)/(Sqrt[Cos[a+b*x]]*Sqrt[c*Sec[a+b*x]])*Int[Cos[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sin[a_.+b_.*x_]^m_*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n+1/2)/(Sqrt[Sin[a+b*x]]*Sqrt[c*Csc[a+b*x]])*Int[Sin[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[cos[a_.+b_.*x_]^m_*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]^n*(c*Sec[a+b*x])^n*Int[Cos[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[sin[a_.+b_.*x_]^m_*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  Sin[a+b*x]^n*(c*Csc[a+b*x])^n*Int[Sin[a+b*x]^(m-n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[tan[a_.+b_.*x_]^m_.*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sec[a+b*x])^n/Sec[a+b*x]^n*Int[Tan[a+b*x]^m*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[cot[a_.+b_.*x_]^m_.*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Csc[a+b*x])^n/Csc[a+b*x]^n*Int[Cot[a+b*x]^m*Csc[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[cot[a_.+b_.*x_]^m_.*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]^n*(c*Sec[a+b*x])^n*Int[Cot[a+b*x]^m/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[tan[a_.+b_.*x_]^m_.*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  Sin[a+b*x]^n*(c*Csc[a+b*x])^n*Int[Tan[a+b*x]^m/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


(* Int[sec[a_.+b_.*x_]^m_.*(c_*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^n*Int[Sec[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && (IntegerQ[n] || PositiveQ[c]) *)


(* Int[csc[a_.+b_.*x_]^m_.*(c_*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  c^n*Int[Csc[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && (IntegerQ[n] || PositiveQ[c]) *)


Int[sec[a_.+b_.*x_]^m_.*(c_*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  1/c^m*Int[(c*Sec[a+b*x])^(m+n),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[csc[a_.+b_.*x_]^m_.*(c_*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  1/c^m*Int[(c*Csc[a+b*x])^(m+n),x] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[sec[a_.+b_.*x_]^m_*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n-1/2)*Sqrt[c*Sec[a+b*x]]/Sqrt[Sec[a+b*x]]*Int[Sec[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[csc[a_.+b_.*x_]^m_*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n-1/2)*Sqrt[c*Csc[a+b*x]]/Sqrt[Csc[a+b*x]]*Int[Csc[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sec[a_.+b_.*x_]^m_*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n+1/2)*Sqrt[Sec[a+b*x]]/Sqrt[c*Sec[a+b*x]]*Int[Sec[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[csc[a_.+b_.*x_]^m_*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  c^(n+1/2)*Sqrt[Csc[a+b*x]]/Sqrt[c*Csc[a+b*x]]*Int[Csc[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sec[a_.+b_.*x_]^m_*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sec[a+b*x])^n/Sec[a+b*x]^n*Int[Sec[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[csc[a_.+b_.*x_]^m_*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Csc[a+b*x])^n/Csc[a+b*x]^n*Int[Csc[a+b*x]^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[csc[a_.+b_.*x_]^m_.*(c_*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Sec[a+b*x])^n/Sec[a+b*x]^n*Int[Csc[a+b*x]^m*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[sec[a_.+b_.*x_]^m_.*(c_*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  (c*Csc[a+b*x])^n/Csc[a+b*x]^n*Int[Sec[a+b*x]^m*Csc[a+b*x]^n,x] /;
FreeQ[{a,b,c,m,n},x]


(* ::Subsection::Closed:: *)
(*5.1 (a+b trig(c+d x))^n*)


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
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n-1)/(d*n) +
  a*(2*n-1)/n*Int[(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]/(d*(b+a*Sin[c+d*x])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Sin[c+d*x]/(d*(b+a*Cos[c+d*x])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*Rt[a,2]*ArcTanh[Rt[a,2]*Cos[c+d*x]/(Sqrt[2]*Sqrt[a+b*Sin[c+d*x]])]/(b*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[a]


Int[1/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*Rt[a,2]*ArcTanh[Rt[a,2]*Sin[c+d*x]/(Sqrt[2]*Sqrt[a+b*Cos[c+d*x]])]/(b*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[a]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*Rt[-a,2]*ArcTan[Rt[-a,2]*Cos[c+d*x]/(Sqrt[2]*Sqrt[a+b*Sin[c+d*x]])]/(b*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[a]


Int[1/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*Rt[-a,2]*ArcTan[Rt[-a,2]*Sin[c+d*x]/(Sqrt[2]*Sqrt[a+b*Cos[c+d*x]])]/(b*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[a]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(a*d*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


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
  -2*Sqrt[a-b]/d*EllipticE[Pi/2-(c+d*x)/2,-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a-b]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[a+b*Sin[c+d*x]]/Sqrt[(a+b*Sin[c+d*x])/(a+b)]*Int[Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[a+b*Cos[c+d*x]]/Sqrt[(a+b*Cos[c+d*x])/(a+b)]*Int[Sqrt[a/(a+b)+b/(a+b)*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[Simp[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[Simp[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1


(* Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -Int[1/(-a-b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && NegativeQ[a] *)


(* Int[1/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -Int[1/(-a-b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && NegativeQ[a] *)


(* Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  x/Rt[a^2-b^2,2] + 
  2/(d*Rt[a^2-b^2,2])*ArcTan[b*Cos[c+d*x]/(a+Rt[a^2-b^2,2]+b*Sin[c+d*x])] /;
FreeQ[{a,b,c,d},x] && PositiveQ[a^2-b^2] && PositiveQ[a] *)


(* Int[1/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  x/Rt[a^2-b^2,2] - 
  2/(d*Rt[a^2-b^2,2])*ArcTan[b*Sin[c+d*x]/(a+Rt[a^2-b^2,2]+b*Cos[c+d*x])] /;
FreeQ[{a,b,c,d},x] && PositiveQ[a^2-b^2] && PositiveQ[a] *)


(* Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Log[RemoveContent[b-Rt[-a^2+b^2,2]*Cos[c+d*x]+a*Sin[c+d*x],x]]/(2*d*Rt[-a^2+b^2,2]) - 
  Log[RemoveContent[b+Rt[-a^2+b^2,2]*Cos[c+d*x]+a*Sin[c+d*x],x]]/(2*d*Rt[-a^2+b^2,2]) /;
FreeQ[{a,b,c,d},x] && NegativeQ[a^2-b^2] && PosQ[a] *)


(* Int[1/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Log[RemoveContent[b+a*Cos[c+d*x]+Sqrt[-a^2+b^2]*Sin[c+d*x],x]]/(2*d*Sqrt[-a^2+b^2]) - 
  Log[RemoveContent[b+a*Cos[c+d*x]-Sqrt[-a^2+b^2]*Sin[c+d*x],x]]/(2*d*Sqrt[-a^2+b^2]) /;
FreeQ[{a,b,c,d},x] && NegativeQ[a^2-b^2] && PosQ[a] *)


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
  -2/(d*Sqrt[a-b])*EllipticF[Pi/2-(c+d*x)/2,-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a-b]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[(a+b*Sin[c+d*x])/(a+b)]/Sqrt[a+b*Sin[c+d*x]]*Int[1/Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[1/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[(a+b*Cos[c+d*x])/(a+b)]/Sqrt[a+b*Cos[c+d*x]]*Int[1/Sqrt[a/(a+b)+b/(a+b)*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*Int[Simp[a*(n+1)-b*(n+2)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*Int[Simp[a*(n+1)-b*(n+2)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
 (a+b*Sin[c+d*x])^(n+1)*Sqrt[b*(1-Sin[c+d*x])/(a+b)]*Sqrt[-b*(1+Sin[c+d*x])/(a-b)]/(b*d*(n+1)*Cos[c+d*x])*
   AppellF1[n+1,1/2,1/2,n+2,(a+b*Sin[c+d*x])/(a-b),(a+b*Sin[c+d*x])/(a+b)] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[n]]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
 -(a+b*Cos[c+d*x])^(n+1)*Sqrt[b*(1-Cos[c+d*x])/(a+b)]*Sqrt[-b*(1+Cos[c+d*x])/(a-b)]/(b*d*(n+1)*Sin[c+d*x])*
   AppellF1[n+1,1/2,1/2,n+2,(a+b*Cos[c+d*x])/(a-b),(a+b*Cos[c+d*x])/(a+b)] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[n]]


Int[(a_+b_.*tan[c_.+d_.*x_])^2,x_Symbol] :=
  (a^2-b^2)*x + b^2*Tan[c+d*x]/d + 2*a*b*Int[Tan[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*cot[c_.+d_.*x_])^2,x_Symbol] :=
  (a^2-b^2)*x - b^2*Cot[c+d*x]/d + 2*a*b*Int[Cot[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -b*Sqrt[2]/(d*Rt[a,2])*ArcTanh[Sqrt[a+b*Tan[c+d*x]]/(Sqrt[2]*Rt[a,2])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && PosQ[a]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  b*Sqrt[2]/(d*Rt[a,2])*ArcTanh[Sqrt[a+b*Cot[c+d*x]]/(Sqrt[2]*Rt[a,2])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && PosQ[a]


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  b*Sqrt[2]/(d*Rt[-a,2])*ArcTan[Sqrt[a+b*Tan[c+d*x]]/(Sqrt[2]*Rt[-a,2])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && NegQ[a]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -b*Sqrt[2]/(d*Rt[-a,2])*ArcTan[Sqrt[a+b*Cot[c+d*x]]/(Sqrt[2]*Rt[-a,2])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && NegQ[a]


(* Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -2*b/d*Subst[Int[1/(2*a-x^2),x],x,Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] *)


(* Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  2*b/d*Subst[Int[1/(2*a-x^2),x],x,Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] *)


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  a^2*e/d*Subst[Int[(a+b*e*x)^(n-1)/(a-b*e*x),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && RationalQ[n] && 0<n<1


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  Module[{e=FreeFactors[Cot[c+d*x],x]},
  -a^2*e/d*Subst[Int[(a+b*e*x)^(n-1)/(a-b*e*x),x],x,Cot[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && RationalQ[n] && 0<n<1


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[c+d*x])^(n-1)/(d*(n-1)) + 
  2*a*Int[(a+b*Tan[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[c+d*x])^(n-1)/(d*(n-1)) + 
  2*a*Int[(a+b*Cot[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a+b*Tan[c+d*x])^n/(2*b*d*n) + 
  1/(2*a)*Int[(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(a+b*Cot[c+d*x])^n/(2*b*d*n) + 
  1/(2*a)*Int[(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Tan[c+d*x])^n/(2*a*d*n)*Hypergeometric2F1[1,n,n+1,(a+b*Tan[c+d*x])/(2*a)] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Cot[c+d*x])^n/(2*a*d*n)*Hypergeometric2F1[1,n,n+1,(a+b*Cot[c+d*x])/(2*a)] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  (a-b*I)/2*Int[(1+I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] +
  (a+b*I)/2*Int[(1-I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  (a-b*I)/2*Int[(1+I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] +
  (a+b*I)/2*Int[(1-I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[c+d*x])^(n-1)/(d*(n-1)) + 
  Int[(a^2-b^2+2*a*b*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[c+d*x])^(n-1)/(d*(n-1)) + 
  Int[(a^2-b^2+2*a*b*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[1/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a*x/(a^2+b^2) + b/(a^2+b^2)*Int[(b-a*Tan[c+d*x])/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[1/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  a*x/(a^2+b^2) + b/(a^2+b^2)*Int[(b-a*Cot[c+d*x])/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Tan[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(a-b*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Cot[c+d*x])^(n+1)/(d*(a^2+b^2)*(n+1)) + 
  1/(a^2+b^2)*Int[(a-b*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2*Int[(1+I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] + 
  1/2*Int[(1-I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2*Int[(1+I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] + 
  1/2*Int[(1-I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[(a_+b_.*sec[c_.+d_.*x_])^2,x_Symbol] :=
  a^2*x + 2*a*b*Int[Sec[c+d*x],x] + b^2*Int[Sec[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*csc[c_.+d_.*x_])^2,x_Symbol] :=
  a^2*x + 2*a*b*Int[Csc[c+d*x],x] + b^2*Int[Csc[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x]


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[a,2]/d*ArcTan[Rt[a,2]*Tan[c+d*x]/Sqrt[a+b*Sec[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[a]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[a,2]/d*ArcTan[Rt[a,2]*Cot[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[a]


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[-a,2]/d*ArcTanh[Rt[-a,2]*Tan[c+d*x]/Sqrt[a+b*Sec[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[a]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[-a,2]/d*ArcTanh[Rt[-a,2]*Cot[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[a]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n-2)/(d*(n-1)) + 
  a/(n-1)*Int[(a*(n-1)+b*(3*n-4)*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-2)/(d*(n-1)) + 
  a/(n-1)*Int[(a*(n-1)+b*(3*n-4)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[1/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  1/a*Int[Sqrt[a+b*Sec[c+d*x]],x] - 
  b/a*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  1/a*Int[Sqrt[a+b*Csc[c+d*x]],x] - 
  b/a*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[(a*(2*n+1)-b*(n+1)*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[(a*(2*n+1)-b*(n+1)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  2*a*(a+b*Sec[c+d*x])^n*Tan[(c+d*x)/2]*(1-Tan[(c+d*x)/2]^2)^n/(d*(a+n*(a-b)))*
    AppellF1[n*(a-b)/(2*a)+1/2,n,1,n*(a-b)/(2*a)+3/2,Tan[(c+d*x)/2]^2,-Tan[(c+d*x)/2]^2] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -2*a*(a+b*Csc[c+d*x])^n*Cot[(c+d*x)/2+Pi/4]*(1-Cot[(c+d*x)/2+Pi/4]^2)^n/(d*(a+n*(a-b)))*
    AppellF1[n*(a-b)/(2*a)+1/2,n,1,n*(a-b)/(2*a)+3/2,Cot[(c+d*x)/2+Pi/4]^2,-Cot[(c+d*x)/2+Pi/4]^2] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  a*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  (a-b)*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  a*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  (a-b)*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  a^2*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  Int[Sec[c+d*x]*(a^2-2*a*b-b^2*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  a^2*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  Int[Csc[c+d*x]*(a^2-2*a*b-b^2*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n-2)/(d*(n-1)) + 
  1/(n-1)*
    Int[Simp[a^3*(n-1)+(b*(b^2*(n-2)+3*a^2*(n-1)))*Sec[c+d*x]+(a*b^2*(3*n-4))*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-2)/(d*(n-1)) + 
  1/(n-1)*
    Int[Simp[a^3*(n-1)+(b*(b^2*(n-2)+3*a^2*(n-1)))*Csc[c+d*x]+(a*b^2*(3*n-4))*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[1/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  x/a - b/a*Int[1/(b+a*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  x/a - b/a*Int[1/(b+a*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] + 
  Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] + 
  Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  1/a*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  1/a*Int[Sec[c+d*x]*(a+b+b*Sec[c+d*x])/(a+b*Sec[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  1/a*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  1/a*Int[Csc[c+d*x]*(a+b+b*Csc[c+d*x])/(a+b*Csc[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[(a^2-b^2)*(n+1)-a*b*(n+1)*Sec[c+d*x]+b^2*(n+2)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<=-2 && NonzeroQ[a^2-b^2] && IntegerQ[2*n]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[(a^2-b^2)*(n+1)-a*b*(n+1)*Csc[c+d*x]+b^2*(n+2)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<=-2 && NonzeroQ[a^2-b^2] && IntegerQ[2*n]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*sin[c_.+d_.*x_]*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[(a+b*Sin[2*c+2*d*x]/2)^n,x] /;
FreeQ[{a,b,c,d,n},x]


(* ::Subsection::Closed:: *)
(*5.2 (a+b trig(c+d x)^n)^p*)


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


Int[1/(a_+b_.*tan[c_.+d_.*x_]^2),x_Symbol] :=
  1/a*Int[Cos[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b]


Int[1/(a_+b_.*cot[c_.+d_.*x_]^2),x_Symbol] :=
  1/a*Int[Sin[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b]


Int[1/(a_+b_.*tan[c_.+d_.*x_]^2),x_Symbol] :=
  x/(a-b) - b/(a-b)*Int[Sec[c+d*x]^2/(a+b*Tan[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b]


Int[1/(a_+b_.*cot[c_.+d_.*x_]^2),x_Symbol] :=
  x/(a-b) - b/(a-b)*Int[Csc[c+d*x]^2/(a+b*Cot[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b]


Int[(a_+b_.*tan[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  e/d*Subst[Int[(a+b*e^2*x^2)^n/(1+e^2*x^2),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[n+1]


Int[(a_+b_.*cot[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  Module[{e=FreeFactors[Cot[c+d*x],x]},
  -e/d*Subst[Int[(a+b*e^2*x^2)^n/(1+e^2*x^2),x],x,Cot[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[n+1]


Int[(a_+b_.*sec[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  Int[(-a*Tan[c+d*x]^2)^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a+b]


Int[(a_+b_.*csc[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  Int[(-a*Cot[c+d*x]^2)^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a+b]


Int[1/(a_+b_.*sec[c_.+d_.*x_]^2),x_Symbol] :=
  x/a - b/a*Int[1/(b+a*Cos[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b]


Int[1/(a_+b_.*csc[c_.+d_.*x_]^2),x_Symbol] :=
  x/a - b/a*Int[1/(b+a*Sin[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b]


Int[(a_+b_.*sec[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/d*Subst[Int[(a+b+b*x^2)^n/(1+x^2),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a+b] && NonzeroQ[n+1]


Int[(a_+b_.*csc[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  -1/d*Subst[Int[(a+b+b*x^2)^n/(1+x^2),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a+b] && NonzeroQ[n+1]


Int[(a_+b_.*tan[c_.+d_.*x_]^m_)^n_,x_Symbol] :=
  1/d*Subst[Int[(a+b*x^m)^n/(1+x^2),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(a_+b_.*cot[c_.+d_.*x_]^m_)^n_,x_Symbol] :=
  -1/d*Subst[Int[(a+b*x^m)^n/(1+x^2),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(a_+b_.*F_[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[Expand[(a+b*F[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && InertTrigQ[F] && IntegerQ[n] && PositiveIntegerQ[p]


Int[1/(a_+b_.*F_[c_.+d_.*x_]^n_),x_Symbol] :=
  Dist[2/(a*n),Sum[Int[1/(1-F[c+d*x]^2/((-1)^(4*k/n)*Rt[-a/b,n/2])),x],{k,1,n/2}],x] /;
FreeQ[{a,b,c,d},x] && InertTrigQ[F] && EvenQ[n] && n>2


Int[1/(a_+b_.*F_[c_.+d_.*x_]^n_),x_Symbol] :=
  Int[ExpandTrig[1/(a+b*F[c+d*x]^n),x],x] /;
FreeQ[{a,b,c,d},x] && InertTrigQ[F] && OddQ[n] && n>2


(* ::Subsection::Closed:: *)
(*5.3 trig(c+d x)^m (a+b trig(c+d x)^n)^p*)


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


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*(e_.*tan[c_.+d_.*x_])^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f^(m+1)/d*Subst[Int[x^m*(a+b*(e*f*x)^n)^p/(1+f^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && IntegerQ[m/2]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*(e_.*cot[c_.+d_.*x_])^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f^(m+1)/d*Subst[Int[x^m*(a+b*(e*f*x)^n)^p/(1+f^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && IntegerQ[m/2]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*ExpandToSum[a*(f*x)^n+b*(1-f^2*x^2)^(n/2),x]^p/(f*x)^(n*p),x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*ExpandToSum[a*(f*x)^n+b*(1-f^2*x^2)^(n/2),x]^p/(f*x)^(n*p),x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*(e_.*tan[c_.+d_.*x_])^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f/d*Subst[Int[(a+b*(e*f*x)^n)^p/(1+f^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && EvenQ[m]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*(e_.*cot[c_.+d_.*x_])^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f/d*Subst[Int[(a+b*(e*f*x)^n)^p/(1+f^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,n,p},x] && EvenQ[m]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f/d*Subst[Int[(1-f^2*x^2)^((m-n*p-1)/2)*ExpandToSum[b*(f*x)^n+a*(1-f^2*x^2)^(n/2),x]^p,x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f/d*Subst[Int[(1-f^2*x^2)^((m-n*p-1)/2)*ExpandToSum[b*(f*x)^n+a*(1-f^2*x^2)^(n/2),x]^p,x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[tan[c_.+d_.*x_]^m_.*(a_+b_.*(e_.*tan[c_.+d_.*x_])^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f/d*Subst[Int[(f*x)^m*(a+b*(e*f*x)^n)^p/(1+f^2*x^2),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*(e_.*cot[c_.+d_.*x_])^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f/d*Subst[Int[(f*x)^m*(a+b*(e*f*x)^n)^p/(1+f^2*x^2),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f^(m+1)/d*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,p},x] && EvenQ[m] && EvenQ[n]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f^(m+1)/d*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,p},x] && EvenQ[m] && EvenQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(b+a*(f*x)^n)^p/(f*x)^(n*p),x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && IntegersQ[n,p]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f/d*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(b+a*(f*x)^n)^p/(f*x)^(n*p),x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && IntegersQ[n,p]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f/d*Subst[Int[(1+f^2*x^2)^(m/2-1)*ExpandToSum[a+b*(1+f^2*x^2)^(n/2),x]^p,x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d,p},x] && EvenQ[m] && EvenQ[n]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f/d*Subst[Int[(1+f^2*x^2)^(m/2-1)*ExpandToSum[a+b*(1+f^2*x^2)^(n/2),x]^p,x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d,p},x] && EvenQ[m] && EvenQ[n]


Int[sec[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  f/d*Subst[Int[ExpandToSum[b+a*(1-f^2*x^2)^(n/2),x]^p/(1-f^2*x^2)^((m+n*p+1)/2),x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[csc[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -f/d*Subst[Int[ExpandToSum[b+a*(1-f^2*x^2)^(n/2),x]^p/(1-f^2*x^2)^((m+n*p+1)/2),x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[sec[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[sec[c+d*x]^m*(a+b*sec[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[m,n,p]


Int[csc[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_]^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[csc[c+d*x]^m*(a+b*csc[c+d*x]^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[m,n,p]


Int[tan[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[c+d*x],x]},
  -1/(d*f^(m+n*p-1))*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(b+a*(f*x)^n)^p/x^(m+n*p),x],x,Cos[c+d*x]/f]] /;
FreeQ[{a,b,c,d,n},x] && OddQ[m] && IntegerQ[n] && IntegerQ[p]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[c+d*x],x]},
  1/(d*f^(m+n*p-1))*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(b+a*(f*x)^n)^p/x^(m+n*p),x],x,Sin[c+d*x]/f]] /;
FreeQ[{a,b,c,d,n},x] && OddQ[m] && IntegerQ[n] && IntegerQ[p]


Int[tan[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[c+d*x],x]},
  f^(m+1)/d*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2),x],x,Tan[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && EvenQ[n]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[c+d*x],x]},
  -f^(m+1)/d*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2),x]^p/(1+f^2*x^2),x],x,Cot[c+d*x]/f]] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && EvenQ[n]


Int[G_[c_.+d_.*x_]^m_./(a_+b_.*F_[c_.+d_.*x_]^n_),x_Symbol] :=
  Int[ExpandTrig[G[c+d*x]^m,1/(a+b*F[c+d*x]^n),x],x] /;
FreeQ[{a,b,c,d,m},x] && InertTrigQ[F,G] && IntegerQ[n] && n>2


(* ::Subsection::Closed:: *)
(*5.4 trig(d+e x)^m (a+b trig(d+e x)^n+c trig(d+e x)^(2 n))^p*)


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


Int[(a_+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Tan[d+e*x]^n+c*Tan[d+e*x]^(2*n))^p/(b+2*c*Tan[d+e*x]^n)^(2*p)*Int[(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cot[d+e*x]^n+c*Cot[d+e*x]^(2*n))^p/(b+2*c*Cot[d+e*x]^n)^(2*p)*Int[(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[1/(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Tan[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Tan[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[1/(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Cot[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Cot[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*(f_.*tan[d_.+e_.*x_])^n_.+c_.*(f_.*tan[d_.+e_.*x_])^n2_.)^p_,x_Symbol] :=
  Module[{g=FreeFactors[Tan[d+e*x],x]},
  g^(m+1)/e*Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2)^(m/2+1),x],x,Tan[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && IntegerQ[m/2]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*(f_.*cot[d_.+e_.*x_])^n_.+c_.*(f_.*cot[d_.+e_.*x_])^n2_.)^p_,x_Symbol] :=
  Module[{g=FreeFactors[Cot[d+e*x],x]},
  -g^(m+1)/e*Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2)^(m/2+1),x],x,Cot[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && IntegerQ[m/2]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*ExpandToSum[a*(g*x)^(2*n)+b*(g*x)^n*(1-g^2*x^2)^(n/2)+c*(1-g^2*x^2)^n,x]^p/(g*x)^(2*n*p),x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*ExpandToSum[a*(g*x)^(2*n)+b*(g*x)^n*(1-g^2*x^2)^(n/2)+c*(1-g^2*x^2)^n,x]^p/(g*x)^(2*n*p),x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*(f_.*tan[d_.+e_.*x_])^n_.+c_.*(f_.*tan[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Tan[d+e*x],x]},
  g/e*Subst[Int[(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2)^(m/2+1),x],x,Tan[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && EvenQ[m]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*(f_.*cot[d_.+e_.*x_])^n_.+c_.*(f_.*cot[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cot[d+e*x],x]},
  -g/e*Subst[Int[(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2)^(m/2+1),x],x,Cot[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && EvenQ[m]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g/e*Subst[Int[(1-g^2*x^2)^((m-2*n*p-1)/2)*ExpandToSum[c*x^(2*n)+b*x^n*(1-x^2)^(n/2)+a*(1-x^2)^n,x]^p,x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g/e*Subst[Int[(1-g^2*x^2)^((m-2*n*p-1)/2)*ExpandToSum[c*x^(2*n)+b*x^n*(1-x^2)^(n/2)+a*(1-x^2)^n,x]^p,x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && EvenQ[n] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Tan[d+e*x]^m*(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Cot[d+e*x]^m*(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Tan[d+e*x]^n+c*Tan[d+e*x]^(2*n))^p/(b+2*c*Tan[d+e*x]^n)^(2*p)*Int[Tan[d+e*x]^m*(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cot[d+e*x]^n+c*Cot[d+e*x]^(2*n))^p/(b+2*c*Cot[d+e*x]^n)^(2*p)*Int[Cot[d+e*x]^m*(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*tan[d_.+e_.*x_])^n_.+c_.*(f_.*tan[d_.+e_.*x_])^n2_.)^p_,x_Symbol] :=
  Module[{g=FreeFactors[Tan[d+e*x],x]},
  g/e*Subst[Int[(g*x)^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2),x],x,Tan[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*cot[d_.+e_.*x_])^n_.+c_.*(f_.*cot[d_.+e_.*x_])^n2_.)^p_,x_Symbol] :=
  Module[{g=FreeFactors[Cot[d+e*x],x]},
  -g/e*Subst[Int[(g*x)^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1+g^2*x^2),x],x,Cot[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Cot[d+e*x]^m*(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Tan[d+e*x]^m*(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_.+c_.*tan[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Tan[d+e*x]^n+c*Tan[d+e*x]^(2*n))^p/(b+2*c*Tan[d+e*x]^n)^(2*p)*Int[Cot[d+e*x]^m*(b+2*c*Tan[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_.+c_.*cot[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cot[d+e*x]^n+c*Cot[d+e*x]^(2*n))^p/(b+2*c*Cot[d+e*x]^n)^(2*p)*Int[Tan[d+e*x]^m*(b+2*c*Cot[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*tan[d_.+e_.*x_]^n_+c_.*tan[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cot[d+e*x],x]},
  g/e*Subst[Int[(g*x)^(m-2*n*p)*(c+b*(g*x)^n+a*(g*x)^(2*n))^p/(1+g^2*x^2),x],x,Cot[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && EvenQ[n]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cot[d_.+e_.*x_]^n_+c_.*cot[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Tan[d+e*x],x]},
  -g/e*Subst[Int[(g*x)^(m-2*n*p)*(c+b*(g*x)^n+a*(g*x)^(2*n))^p/(1+g^2*x^2),x],x,Tan[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && EvenQ[n]


Int[(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Sec[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Csc[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sec[d+e*x]^n+c*Sec[d+e*x]^(2*n))^p/(b+2*c*Sec[d+e*x]^n)^(2*p)*Int[u*(b+2*c*Sec[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Csc[d+e*x]^n+c*Csc[d+e*x]^(2*n))^p/(b+2*c*Csc[d+e*x]^n)^(2*p)*Int[u*(b+2*c*Csc[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[1/(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Sec[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Sec[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[1/(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Csc[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Csc[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[d+e*x],x]},
  -f/e*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(b+a*(f*x)^n)^p/(f*x)^(n*p),x],x,Cos[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && IntegersQ[n,p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[d+e*x],x]},
  f/e*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(b+a*(f*x)^n)^p/(f*x)^(n*p),x],x,Sin[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && OddQ[m] && IntegersQ[n,p]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*sec[d_.+e_.*x_]^n_+c_.*sec[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2)+c*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(m/2+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[n2-2*n] && EvenQ[m] && EvenQ[n]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*csc[d_.+e_.*x_]^n_+c_.*csc[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2)+c*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(m/2+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[n2-2*n] && EvenQ[m] && EvenQ[n]


Int[sec[d_.+e_.*x_]^m_.*(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Sec[d+e*x]^m*(b+2*c*Sec[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[csc[d_.+e_.*x_]^m_.*(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Csc[d+e*x]^m*(b+2*c*Csc[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[sec[d_.+e_.*x_]^m_.*(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sec[d+e*x]^n+c*Sec[d+e*x]^(2*n))^p/(b+2*c*Sec[d+e*x]^n)^(2*p)*Int[Sec[d+e*x]^m*(b+2*c*Sec[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[csc[d_.+e_.*x_]^m_.*(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Csc[d+e*x]^n+c*Csc[d+e*x]^(2*n))^p/(b+2*c*Csc[d+e*x]^n)^(2*p)*Int[Csc[d+e*x]^m*(b+2*c*Csc[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[sec[d_.+e_.*x_]^m_.*(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  Int[ExpandTrig[sec[d+e*x]^m*(a+b*sec[d+e*x]^n+c*sec[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && IntegersQ[m,n,p]


Int[csc[d_.+e_.*x_]^m_.*(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  Int[ExpandTrig[csc[d+e*x]^m*(a+b*csc[d+e*x]^n+c*csc[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && IntegersQ[m,n,p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[d+e*x],x]},
  -1/(e*f^(m+n*p-1))*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(c+b*(f*x)^n+c*(f*x)^(2*n))^p/x^(m+2*n*p),x],x,Cos[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && OddQ[m] && IntegerQ[n] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*csc[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[d+e*x],x]},
  1/(e*f^(m+n*p-1))*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(c+b*(f*x)^n+c*(f*x)^(2*n))^p/x^(m+2*n*p),x],x,Sin[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && OddQ[m] && IntegerQ[n] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*sec[d_.+e_.*x_]^n_+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2)+c*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && EvenQ[n]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*csc[d_.+e_.*x_]^n_+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2)+c*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && EvenQ[m] && EvenQ[n]


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
(*6.1 (A+B trig(c+d x)) (a+b trig(c+d x))^n*)


Int[(A_+B_.*sin[c_.+d_.*x_])*(b_*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Int[(b*Sin[c+d*x])^n,x] + B/b*Int[(b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{b,c,d,A,B,n},x]


Int[(A_+B_.*cos[c_.+d_.*x_])*(b_*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Int[(b*Cos[c+d*x])^n,x] + B/b*Int[(b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{b,c,d,A,B,n},x]


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  -B*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1)) /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[a^2-b^2] && ZeroQ[B*a*n+A*b*(n+1)]


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  B*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(d*(n+1)) /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[a^2-b^2] && ZeroQ[B*a*n+A*b*(n+1)]


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[A*b-a*B]


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[A*b-a*B]


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  (2*a*A+b*B)*x/2 - b*B*Cos[c+d*x]*Sin[c+d*x]/(2*d) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A*b+a*B]


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  (2*a*A+b*B)*x/2 + b*B*Cos[c+d*x]*Sin[c+d*x]/(2*d) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A*b+a*B]


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  (2*a*A+b*B)*x/2 - b*B*Cos[c+d*x]*Sin[c+d*x]/(2*d) + (A*b+a*B)*Int[Sin[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[A*b+a*B]


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  (2*a*A+b*B)*x/2 + b*B*Cos[c+d*x]*Sin[c+d*x]/(2*d) + (A*b+a*B)*Int[Cos[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[A*b+a*B]


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1)) + 
  (a*B*n+A*b*(n+1))/(b*(n+1))*Int[(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n>0 && ZeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  B*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(d*(n+1)) + 
  (a*B*n+A*b*(n+1))/(b*(n+1))*Int[(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n>0 && ZeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1)) + 
  1/(n+1)*Int[Simp[b*B*n+a*A*(n+1)+(a*B*n+A*b*(n+1))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n>0 && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  B*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(d*(n+1)) + 
  1/(n+1)*Int[Simp[b*B*n+a*A*(n+1)+(a*B*n+A*b*(n+1))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n>0 && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_])/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  B*x/b + (A*b-a*B)/b*Int[1/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[(A_+B_.*cos[c_.+d_.*x_])/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  B*x/b + (A*b-a*B)/b*Int[1/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[(A_+B_.*sin[c_.+d_.*x_])/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cos[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]]) + (A*b-a*B)/b*Int[1/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*B*Sin[c+d*x]/(d*Sqrt[a+b*Cos[c+d*x]]) + (A*b-a*B)/b*Int[1/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_])/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  B/b*Int[Sqrt[a+b*Sin[c+d*x]],x] +
  (A*b-a*B)/b*Int[1/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  B/b*Int[Sqrt[a+b*Cos[c+d*x]],x] +
  (A*b-a*B)/b*Int[1/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) + 
  (a*B*n+A*b*(n+1))/(a*b*(2*n+1))*Int[(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(a*d*(2*n+1)) + 
  (a*B*n+A*b*(n+1))/(a*b*(2*n+1))*Int[(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) +
  1/((n+1)*(a^2-b^2))*
    Int[Simp[(a*A-b*B)*(n+1)-(A*b-a*B)*(n+2)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) +
  1/((n+1)*(a^2-b^2))*
    Int[Simp[(a*A-b*B)*(n+1)-(A*b-a*B)*(n+2)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  B/b*Int[(a+b*Sin[c+d*x])^(n+1),x] + (A*b-a*B)/b*Int[(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && Not[IntegerQ[n]]


Int[(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  B/b*Int[(a+b*Cos[c+d*x])^(n+1),x] + (A*b-a*B)/b*Int[(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && Not[IntegerQ[n]]


Int[(A_+B_.*tan[c_.+d_.*x_])*(b_*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Int[(b*Tan[c+d*x])^n,x] + B/b*Int[(b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{b,c,d,A,B,n},x]


Int[(A_+B_.*cot[c_.+d_.*x_])*(b_*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Int[(b*Cot[c+d*x])^n,x] + B/b*Int[(b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{b,c,d,A,B,n},x]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  (a*A-b*B)*x + b*B*Tan[c+d*x]/d + (A*b+a*B)*Int[Tan[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B},x]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  (a*A-b*B)*x - b*B*Cot[c+d*x]/d + (A*b+a*B)*Int[Cot[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B},x]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  B/b*Int[(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[A*b-a*B]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  B/b*Int[(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[A*b-a*B]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  B*(a+b*Tan[c+d*x])^n/(d*n) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*(a+b*Cot[c+d*x])^n/(d*n) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  (A*b+a*B)/(2*a*b)*Int[(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B] && RationalQ[n] && n<0


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  (A*b+a*B)/(2*a*b)*Int[(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B] && RationalQ[n] && n<0


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  B*(a+b*Tan[c+d*x])^n/(d*n) + (A*b+a*B)/b*Int[(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B] && Not[RationalQ[n] && n<0]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*(a+b*Cot[c+d*x])^n/(d*n) + (A*b+a*B)/b*Int[(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B] && Not[RationalQ[n] && n<0]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  B*(a+b*Tan[c+d*x])^n/(d*n) + 
  Int[Simp[a*A-b*B+(A*b+a*B)*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>0


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*(a+b*Cot[c+d*x])^n/(d*n) + 
  Int[Simp[a*A-b*B+(A*b+a*B)*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>0


Int[(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  A/(b*d)*Log[RemoveContent[a*Cos[c+d*x]+b*Sin[c+d*x],x]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[a*A+b*B]


Int[(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -A/(b*d)*Log[RemoveContent[b*Cos[c+d*x]+a*Sin[c+d*x],x]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[a*A+b*B]


Int[(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  (a*A+b*B)*x/(a^2+b^2) + (A*b-a*B)/(a^2+b^2)*Int[(b-a*Tan[c+d*x])/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[a*A+b*B]


Int[(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  (a*A+b*B)*x/(a^2+b^2) + (A*b-a*B)/(a^2+b^2)*Int[(b-a*Cot[c+d*x])/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[a*A+b*B]


Int[(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -2*B/d*Rt[B/(A*b+a*B),2]*ArcTanh[Rt[B/(A*b+a*B),2]*Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && PosQ[B/(A*b+a*B)]


Int[(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  2*B/d*Rt[B/(A*b+a*B),2]*ArcTanh[Rt[B/(A*b+a*B),2]*Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && PosQ[B/(A*b+a*B)]


Int[(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  2*B/d*Rt[-B/(A*b+a*B),2]*ArcTan[Rt[-B/(A*b+a*B),2]*Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && NegQ[B/(A*b+a*B)]


Int[(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -2*B/d*Rt[-B/(A*b+a*B),2]*ArcTan[Rt[-B/(A*b+a*B),2]*Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && NegQ[B/(A*b+a*B)]


Int[(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*B^2*ArcTan[(Sqrt[A*b*B]+Sqrt[2]*B*Sqrt[a+b*Tan[c+d*x]])/Sqrt[B*(A*b-2*a*B)]]/(d*Sqrt[B*(A*b-2*a*B)]) - 
  Sqrt[2]*B^2*ArcTan[(Sqrt[A*b*B]-Sqrt[2]*B*Sqrt[a+b*Tan[c+d*x]])/Sqrt[B*(A*b-2*a*B)]]/(d*Sqrt[B*(A*b-2*a*B)]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2*b-2*a*A*B-b*B^2] && PosQ[A*b*B] && PosQ[B*(A*b-2*a*B)]


Int[(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*B^2*ArcTan[(Sqrt[A*b*B]+Sqrt[2]*B*Sqrt[a+b*Cot[c+d*x]])/Sqrt[B*(A*b-2*a*B)]]/(d*Sqrt[B*(A*b-2*a*B)]) + 
  Sqrt[2]*B^2*ArcTan[(Sqrt[A*b*B]-Sqrt[2]*B*Sqrt[a+b*Cot[c+d*x]])/Sqrt[B*(A*b-2*a*B)]]/(d*Sqrt[B*(A*b-2*a*B)]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2*b-2*a*A*B-b*B^2] && PosQ[A*b*B] && PosQ[B*(A*b-2*a*B)]


Int[(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*B^2*ArcTanh[(Sqrt[A*b*B]+Sqrt[2]*B*Sqrt[a+b*Tan[c+d*x]])/Sqrt[-B*(A*b-2*a*B)]]/(d*Sqrt[-B*(A*b-2*a*B)]) + 
  Sqrt[2]*B^2*ArcTanh[(Sqrt[A*b*B]-Sqrt[2]*B*Sqrt[a+b*Tan[c+d*x]])/Sqrt[-B*(A*b-2*a*B)]]/(d*Sqrt[-B*(A*b-2*a*B)]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2*b-2*a*A*B-b*B^2] && PosQ[A*b*B] && NegQ[B*(A*b-2*a*B)]


Int[(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*B^2*ArcTanh[(Sqrt[A*b*B]+Sqrt[2]*B*Sqrt[a+b*Cot[c+d*x]])/Sqrt[-B*(A*b-2*a*B)]]/(d*Sqrt[-B*(A*b-2*a*B)]) - 
  Sqrt[2]*B^2*ArcTanh[(Sqrt[A*b*B]-Sqrt[2]*B*Sqrt[a+b*Cot[c+d*x]])/Sqrt[-B*(A*b-2*a*B)]]/(d*Sqrt[-B*(A*b-2*a*B)]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2*b-2*a*A*B-b*B^2] && PosQ[A*b*B] && NegQ[B*(A*b-2*a*B)]


Int[(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  B^2*Log[RemoveContent[A*b-2*a*B-b*B*Tan[c+d*x]+Sqrt[2]*Sqrt[-B*(A*b-2*a*B)]*Sqrt[a+b*Tan[c+d*x]],x]]/(Sqrt[2]*Sqrt[-B*(A*b-2*a*B)]*d) - 
  B^2*Log[RemoveContent[A*b-2*a*B-b*B*Tan[c+d*x]-Sqrt[2]*Sqrt[-B*(A*b-2*a*B)]*Sqrt[a+b*Tan[c+d*x]],x]]/(Sqrt[2]*Sqrt[-B*(A*b-2*a*B)]*d) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2*b-2*a*A*B-b*B^2] && NegQ[B*(A*b-2*a*B)]


Int[(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -B^2*Log[RemoveContent[A*b-2*a*B-b*B*Cot[c+d*x]+Sqrt[2]*Sqrt[-B*(A*b-2*a*B)]*Sqrt[a+b*Cot[c+d*x]],x]]/(Sqrt[2]*Sqrt[-B*(A*b-2*a*B)]*d) + 
  B^2*Log[RemoveContent[A*b-2*a*B-b*B*Cot[c+d*x]-Sqrt[2]*Sqrt[-B*(A*b-2*a*B)]*Sqrt[a+b*Cot[c+d*x]],x]]/(Sqrt[2]*Sqrt[-B*(A*b-2*a*B)]*d) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2*b-2*a*A*B-b*B^2] && NegQ[B*(A*b-2*a*B)]


Int[(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  1/(2*(a^2+b^2))*Int[(A*(a^2+b^2)+Sqrt[a^2+b^2]*(a*A+b*B)+(a^2*B+b^2*B+Sqrt[a^2+b^2]*(A*b-a*B))*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] + 
  1/(2*(a^2+b^2))*Int[(A*(a^2+b^2)-Sqrt[a^2+b^2]*(a*A+b*B)+(a^2*B+b^2*B-Sqrt[a^2+b^2]*(A*b-a*B))*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[A^2*b-2*a*A*B-b*B^2] && RationalQ[a,b,A,B]


Int[(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  1/(2*(a^2+b^2))*Int[(A*(a^2+b^2)+Sqrt[a^2+b^2]*(a*A+b*B)+(a^2*B+b^2*B+Sqrt[a^2+b^2]*(A*b-a*B))*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] + 
  1/(2*(a^2+b^2))*Int[(A*(a^2+b^2)-Sqrt[a^2+b^2]*(a*A+b*B)+(a^2*B+b^2*B-Sqrt[a^2+b^2]*(A*b-a*B))*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[A^2*b-2*a*A*B-b*B^2] && RationalQ[a,b,A,B]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*(a+b*Tan[c+d*x])^(n+1)/(d*(a^2+b^2)*(n+1)) + 
  1/(a^2+b^2)*Int[Simp[a*A+b*B-(A*b-a*B)*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*(a+b*Cot[c+d*x])^(n+1)/(d*(a^2+b^2)*(n+1)) + 
  1/(a^2+b^2)*Int[Simp[a*A+b*B-(A*b-a*B)*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


(* Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*B/d*Subst[Int[(a+b*x)^n/(B+A*x),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && RationalQ[n] && -1<n<0 *)


(* Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*B/d*Subst[Int[(a+b*x)^n/(B+A*x),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && RationalQ[n] && -1<n<0 *)


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*B*(a+b*Tan[c+d*x])^(n+1)/(d*(n+1)*(a*A-b*B))*Hypergeometric2F1[1,n+1,n+2,A*(a+b*Tan[c+d*x])/(a*A-b*B)] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]] && ZeroQ[A^2+B^2]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  A*B*(a+b*Cot[c+d*x])^(n+1)/(d*(n+1)*(a*A-b*B))*Hypergeometric2F1[1,n+1,n+2,A*(a+b*Cot[c+d*x])/(a*A-b*B)] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]] && ZeroQ[A^2+B^2]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(I*A+B)/2*Int[(I-Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] - 
  (I*A-B)/2*Int[(I+Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]] && NonzeroQ[A^2+B^2]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(I*A+B)/2*Int[(I-Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] - 
  (I*A-B)/2*Int[(I+Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]] && NonzeroQ[A^2+B^2]


Int[(A_+B_.*sec[c_.+d_.*x_])*(b_*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Int[(b*Sec[c+d*x])^n,x] + B/b*Int[(b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{b,c,d,A,B,n},x]


Int[(A_+B_.*csc[c_.+d_.*x_])*(b_*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Int[(b*Csc[c+d*x])^n,x] + B/b*Int[(b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{b,c,d,A,B,n},x]


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[A*b-a*B]


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[A*b-a*B]


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  a*A*x + b*B*Int[Sec[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A*b+a*B]


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  a*A*x + b*B*Int[Csc[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A*b+a*B]


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  a*A*x + (A*b+a*B)*Int[Sec[c+d*x],x] + b*B*Int[Sec[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[A*b+a*B]


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  a*A*x + (A*b+a*B)*Int[Csc[c+d*x],x] + b*B*Int[Csc[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[A*b+a*B]


Int[(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  A*Int[Sqrt[a+b*Sec[c+d*x]],x] + 
  B*Int[Sec[c+d*x]*Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Int[Sqrt[a+b*Csc[c+d*x]],x] + 
  B*Int[Csc[c+d*x]*Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b*B*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[Simp[a*A*n+(a*B*(2*n-1)+A*b*n)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n>1 && ZeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*B*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[Simp[a*A*n+(a*B*(2*n-1)+A*b*n)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n>1 && ZeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Int[(a*A+(A*b+(a+b)*B)*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  b*B*Int[Sec[c+d*x]*(1-Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Int[(a*A+(A*b+(a+b)*B)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  b*B*Int[Csc[c+d*x]*(1-Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b*B*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n-1)/(d*n) + 
  1/n*
    Int[Simp[a^2*A*n+(b^2*B*(n-1)+2*a*A*b*n+a^2*B*n)*Sec[c+d*x]+b*(A*b*n+a*B*(2*n-1))*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n>1 && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*B*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  1/n*
    Int[Simp[a^2*A*n+(b^2*B*(n-1)+2*a*A*b*n+a^2*B*n)*Csc[c+d*x]+b*(A*b*n+a*B*(2*n-1))*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n>1 && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_])/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  A*x/a - (A*b-a*B)/a*Int[1/(b+a*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[(A_+B_.*csc[c_.+d_.*x_])/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  A*x/a - (A*b-a*B)/a*Int[1/(b+a*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  A/a*Int[Sqrt[a+b*Sec[c+d*x]],x] - 
  (A*b-a*B)/a*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[b*A-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A/a*Int[Sqrt[a+b*Csc[c+d*x]],x] - 
  (A*b-a*B)/a*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[b*A-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[b+a*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Sec[c+d*x]])*
    Int[(A+A*Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[b+a*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B]


Int[(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]])*
    Int[(A+A*Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[b+a*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B]


Int[(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  A*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  (A-B)*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]


Int[(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  (A-B)*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(b^2*(2*n+1))*Int[Simp[a*A*(2*n+1)-(A*b-a*B)*(n+1)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(b^2*(2*n+1))*Int[Simp[a*A*(2*n+1)-(A*b-a*B)*(n+1)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_])/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  1/(a*(a-b))*Int[(A*(a-b)-(A*b-a*B)*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] + 
  b*(A*b-a*B)/(a*(a-b))*Int[Sec[c+d*x]*(1+Sec[c+d*x])/(a+b*Sec[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  1/(a*(a-b))*Int[(A*(a-b)-(A*b-a*B)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  b*(A*b-a*B)/(a*(a-b))*Int[Csc[c+d*x]*(1+Csc[c+d*x])/(a+b*Csc[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(A*b-a*B)*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[A*(a^2-b^2)*(n+1)-(a*(A*b-a*B)*(n+1))*Sec[c+d*x]+b*(A*b-a*B)*(n+2)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2] && n!=-3/2


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(A*b-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[A*(a^2-b^2)*(n+1)-(a*(A*b-a*B)*(n+1))*Csc[c+d*x]+b*(A*b-a*B)*(n+2)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2] && n!=-3/2


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  B/b*Int[(a+b*Sec[c+d*x])^(n+1),x] + (A*b-a*B)/b*Int[(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && Not[IntegerQ[n]]


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  B/b*Int[(a+b*Csc[c+d*x])^(n+1),x] + (A*b-a*B)/b*Int[(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && Not[IntegerQ[n]]


(* ::Subsection::Closed:: *)
(*6.2 (A+B trig(d+e x)) (a+b trig(d+e x)+c trig(d+e x)^2)^n*)


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


Int[(A_+B_.*tan[d_.+e_.*x_])*(a_+b_.*tan[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Tan[d+e*x])*(b+2*c*Tan[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*cot[d_.+e_.*x_])*(a_+b_.*cot[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Cot[d+e*x])*(b+2*c*Cot[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*tan[d_.+e_.*x_])*(a_+b_.*tan[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Tan[d+e*x]+c*Tan[d+e*x]^2)^n/(b+2*c*Tan[d+e*x])^(2*n)*Int[(A+B*Tan[d+e*x])*(b+2*c*Tan[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*cot[d_.+e_.*x_])*(a_+b_.*cot[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Cot[d+e*x]+c*Cot[d+e*x]^2)^n/(b+2*c*Cot[d+e*x])^(2*n)*Int[(A+B*Cot[d+e*x])*(b+2*c*Cot[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*tan[d_.+e_.*x_])/(a_.+b_.*tan[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Tan[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Tan[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*cot[d_.+e_.*x_])/(a_.+b_.*cot[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Cot[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Cot[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*tan[d_.+e_.*x_])*(a_.+b_.*tan[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*tan[d+e*x])*(a+b*tan[d+e*x]+c*tan[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*cot[d_.+e_.*x_])*(a_.+b_.*cot[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*cot[d+e*x])*(a+b*cot[d+e*x]+c*cot[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*sec[d_.+e_.*x_])*(a_+b_.*sec[d_.+e_.*x_]+c_.*sec[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Sec[d+e*x])*(b+2*c*Sec[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*csc[d_.+e_.*x_])*(a_+b_.*csc[d_.+e_.*x_]+c_.*csc[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Csc[d+e*x])*(b+2*c*Csc[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*sec[d_.+e_.*x_])*(a_+b_.*sec[d_.+e_.*x_]+c_.*sec[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Sec[d+e*x]+c*Sec[d+e*x]^2)^n/(b+2*c*Sec[d+e*x])^(2*n)*Int[(A+B*Sec[d+e*x])*(b+2*c*Sec[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*csc[d_.+e_.*x_])*(a_+b_.*csc[d_.+e_.*x_]+c_.*csc[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Csc[d+e*x]+c*Csc[d+e*x]^2)^n/(b+2*c*Csc[d+e*x])^(2*n)*Int[(A+B*Csc[d+e*x])*(b+2*c*Csc[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*sec[d_.+e_.*x_])/(a_.+b_.*sec[d_.+e_.*x_]+c_.*sec[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Sec[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Sec[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*csc[d_.+e_.*x_])/(a_.+b_.*csc[d_.+e_.*x_]+c_.*csc[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Csc[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Csc[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*sec[d_.+e_.*x_])*(a_.+b_.*sec[d_.+e_.*x_]+c_.*sec[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*sec[d+e*x])*(a+b*sec[d+e*x]+c*sec[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*csc[d_.+e_.*x_])*(a_.+b_.*csc[d_.+e_.*x_]+c_.*csc[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*csc[d+e*x])*(a+b*csc[d+e*x]+c*csc[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-4*a*c] && IntegerQ[n]


(* ::Subsection::Closed:: *)
(*7.1.1 sin(c+d x)^m (a+b sin(c+d x))^n*)


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  a*Int[Sin[c+d*x]^m,x] + b*Int[Sin[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,m},x]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  a*Int[Cos[c+d*x]^m,x] + b*Int[Cos[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,m},x]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_])^2,x_Symbol] :=
  2*a*b*Int[Sin[c+d*x]^(m+1),x] + Int[Sin[c+d*x]^m*(a^2+b^2*Sin[c+d*x]^2),x] /;
FreeQ[{a,b,c,d,m},x]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_])^2,x_Symbol] :=
  2*a*b*Int[Cos[c+d*x]^(m+1),x] + Int[Cos[c+d*x]^m*(a^2+b^2*Cos[c+d*x]^2),x] /;
FreeQ[{a,b,c,d,m},x]


Int[sin[c_.+d_.*x_]/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  x/b - a/b*Int[1/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[cos[c_.+d_.*x_]/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  x/b - a/b*Int[1/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[sin[c_.+d_.*x_]^2/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]/(b*d) - a/b*Int[Sin[c+d*x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[cos[c_.+d_.*x_]^2/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Sin[c+d*x]/(b*d) - a/b*Int[Cos[c+d*x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[1/Sin[c+d*x],x] - b/a*Int[1/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[1/Cos[c+d*x],x] - b/a*Int[1/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(m-1)/(d*(a+b*Sin[c+d*x])) + m/b*Int[Sin[c+d*x]^(m-1),x] - (m-1)/a*Int[Sin[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(m-1)/(d*(a+b*Cos[c+d*x])) + m/b*Int[Cos[c+d*x]^(m-1),x] - (m-1)/a*Int[Cos[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(a+b*Sin[c+d*x])) - m/a*Int[Sin[c+d*x]^m,x] + (m+1)/b*Int[Sin[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<0


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(a+b*Cos[c+d*x])) - m/a*Int[Cos[c+d*x]^m,x] + (m+1)/b*Int[Cos[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<0


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -a*Cos[c+d*x]*Sin[c+d*x]^m/(b*d*(a+b*Sin[c+d*x])) + 
  m/b*Int[Sin[c+d*x]^(m-1),x] - 
  m/a*Int[Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  a*Sin[c+d*x]*Cos[c+d*x]^m/(b*d*(a+b*Cos[c+d*x])) + 
  m/b*Int[Cos[c+d*x]^(m-1),x] - 
  m/a*Int[Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2]


Int[Sqrt[sin[c_.+d_.*x_]]/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[1/Sqrt[Sin[c+d*x]],x] - 
  a/b*Int[1/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[cos[c_.+d_.*x_]]/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[1/Sqrt[Cos[c+d*x]],x] - 
  a/b*Int[1/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^(3/2)/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[Sqrt[Sin[c+d*x]],x] - 
  a/b*Int[Sqrt[Sin[c+d*x]]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^(3/2)/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[Sqrt[Cos[c+d*x]],x] - 
  a/b*Int[Sqrt[Cos[c+d*x]]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]*Sin[c+d*x]^(m-2)/(b*d*(m-1)) + 
  1/(b*(m-1))*Int[Sin[c+d*x]^(m-3)*Simp[a*(m-2)+b*(m-2)*Sin[c+d*x]-a*(m-1)*Sin[c+d*x]^2,x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>2 && IntegerQ[2*m]


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Sin[c+d*x]*Cos[c+d*x]^(m-2)/(b*d*(m-1)) + 
  1/(b*(m-1))*Int[Cos[c+d*x]^(m-3)*Simp[a*(m-2)+b*(m-2)*Cos[c+d*x]-a*(m-1)*Cos[c+d*x]^2,x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>2 && IntegerQ[2*m]


Int[1/(Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  2/(d*(a+b))*EllipticPi[2*b/(a+b),(c+d*x)/2-Pi/4,2] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])),x_Symbol] :=
  2/(d*(a+b))*EllipticPi[2*b/(a+b),(c+d*x)/2,2] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(m+1)/(a*d*(m+1)) - 
  1/(a*(m+1))*Int[Sin[c+d*x]^(m+1)*Simp[b*(m+1)-a*(m+2)*Sin[c+d*x]-b*(m+2)*Sin[c+d*x]^2,x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(m+1)/(a*d*(m+1)) - 
  1/(a*(m+1))*Int[Cos[c+d*x]^(m+1)*Simp[b*(m+1)-a*(m+2)*Cos[c+d*x]-b*(m+2)*Cos[c+d*x]^2,x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(2*n+1)) + 
  n/(b*(2*n+1))*Int[(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(d*(2*n+1)) + 
  n/(b*(2*n+1))*Int[(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1)) + 
  a*n/(b*(n+1))*Int[(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1]


Int[cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(d*(n+1)) + 
  a*n/(b*(n+1))*Int[(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/sin[c_.+d_.*x_],x_Symbol] :=
  -2*Rt[a,2]/d*ArcTanh[Rt[a,2]*Cos[c+d*x]/Sqrt[a+b*Sin[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[a]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/cos[c_.+d_.*x_],x_Symbol] :=
  2*Rt[a,2]/d*ArcTanh[Rt[a,2]*Sin[c+d*x]/Sqrt[a+b*Cos[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[a]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/sin[c_.+d_.*x_],x_Symbol] :=
  2*Rt[-a,2]/d*ArcTan[Rt[-a,2]*Cos[c+d*x]/Sqrt[a+b*Sin[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[a]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/cos[c_.+d_.*x_],x_Symbol] :=
  -2*Rt[-a,2]/d*ArcTan[Rt[-a,2]*Sin[c+d*x]/Sqrt[a+b*Cos[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[a]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[a,2]/d*ArcSin[Rt[a,2]*Cos[c+d*x]/Sqrt[a+b*Sin[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PosQ[a]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/Sqrt[cos[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[a,2]/d*ArcSin[Rt[a,2]*Sin[c+d*x]/Sqrt[a+b*Cos[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PosQ[a]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[-a,2]/d*ArcSinh[Rt[-a,2]*Cos[c+d*x]/Sqrt[a+b*Sin[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && NegQ[a]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/Sqrt[cos[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[-a,2]/d*ArcSinh[Rt[-a,2]*Sin[c+d*x]/Sqrt[a+b*Cos[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && NegQ[a]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[b,2]/d*ArcTan[Rt[b,2]*Cos[c+d*x]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[b]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/Sqrt[cos[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[b,2]/d*ArcTan[Rt[b,2]*Sin[c+d*x]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[b]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[-b,2]/d*ArcTanh[Rt[-b,2]*Cos[c+d*x]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[b]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/Sqrt[cos[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[-b,2]/d*ArcTanh[Rt[-b,2]*Sin[c+d*x]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[b]


Int[sin[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*b*Cos[c+d*x]*Sin[c+d*x]^m/(d*(2*m+1)*Sqrt[a+b*Sin[c+d*x]]) + 
  2*a*m/(b*(2*m+1))*Int[Sin[c+d*x]^(m-1)*Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-1/2


Int[cos[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*b*Sin[c+d*x]*Cos[c+d*x]^m/(d*(2*m+1)*Sqrt[a+b*Cos[c+d*x]]) + 
  2*a*m/(b*(2*m+1))*Int[Cos[c+d*x]^(m-1)*Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-1/2


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
  -2*a*Cos[c+d*x]/(d*Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/cos[c_.+d_.*x_]^(3/2),x_Symbol] :=
  2*a*Sin[c+d*x]/(d*Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  a*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Sin[c+d*x]]) + 
  b*(2*m+3)/(2*a*(m+1))*Int[Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-3/2


Int[cos[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -a*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Cos[c+d*x]]) + 
  b*(2*m+3)/(2*a*(m+1))*Int[Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-3/2


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Int[Sin[c+d*x]^m*(a+b*Sin[c+d*x])^(n-1),x] + 
  b*Int[Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && 1/2<n<1


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Int[Cos[c+d*x]^m*(a+b*Cos[c+d*x])^(n-1),x] + 
  b*Int[Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && 1/2<n<1


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n*Sin[c+d*x]^n) + 
  b*(2*n-1)/n*Int[(a+b*Sin[c+d*x])^(n-1)/Sin[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m+n+1==0


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n-1)/(d*n*Cos[c+d*x]^n) + 
  b*(2*n-1)/n*Int[(a+b*Cos[c+d*x])^(n-1)/Cos[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m+n+1==0


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1)*Sin[c+d*x]^(n+1)) + 
  a*n/(b*(n+1))*Int[(a+b*Sin[c+d*x])^n/Sin[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m+n+2==0


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(d*(n+1)*Cos[c+d*x]^(n+1)) + 
  a*n/(b*(n+1))*Int[(a+b*Cos[c+d*x])^n/Cos[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m+n+2==0


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-2)/(d*(m+1)) + 
  b/(m+1)*Int[Sin[c+d*x]^(m+1)*(a*(2*m-n+4)+b*(2*m+n+1)*Sin[c+d*x])*(a+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-2)/(d*(m+1)) + 
  b/(m+1)*Int[Cos[c+d*x]^(m+1)*(a*(2*m-n+4)+b*(2*m+n+1)*Cos[c+d*x])*(a+b*Cos[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-2)/(d*(m+n)) + 
  a/(m+n)*Int[Sin[c+d*x]^m*(a*(2*m+n+1)+b*(2*m+3*n-2)*Sin[c+d*x])*(a+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-2)/(d*(m+n)) + 
  a/(m+n)*Int[Cos[c+d*x]^m*(a*(2*m+n+1)+b*(2*m+3*n-2)*Cos[c+d*x])*(a+b*Cos[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1]


Int[1/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  (* -Sqrt[2]/(Sqrt[a]*d)*ArcSin[Cos[c+d*x]/(1+Sin[c+d*x])] /; *)
  Sqrt[2]/(Sqrt[a]*d)*ArcSin[Tan[(c+d*x)/2-Pi/4]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PositiveQ[a]


Int[1/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  (* Sqrt[2]/(Sqrt[a]*d)*ArcSin[Sin[c+d*x]/(1+Cos[c+d*x])] /; *)
  Sqrt[2]/(Sqrt[a]*d)*ArcSin[Tan[(c+d*x)/2]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PositiveQ[a]


Int[1/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  -Sqrt[2]*Rt[b,2]/(a*d)*ArcTan[Rt[b,2]*Cos[c+d*x]/(Sqrt[2]*Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[b]


Int[1/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  Sqrt[2]*Rt[b,2]/(a*d)*ArcTan[Rt[b,2]*Sin[c+d*x]/(Sqrt[2]*Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[b]


Int[1/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  Sqrt[2]*Rt[-b,2]/(a*d)*ArcTanh[Rt[-b,2]*Cos[c+d*x]/(Sqrt[2]*Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[b]


Int[1/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  -Sqrt[2]*Rt[-b,2]/(a*d)*ArcTanh[Rt[-b,2]*Sin[c+d*x]/(Sqrt[2]*Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[b]


Int[Sqrt[sin[c_.+d_.*x_]]/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  1/b*Int[Sqrt[a+b*Sin[c+d*x]]/Sqrt[Sin[c+d*x]],x] - 
  a/b*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[Sqrt[cos[c_.+d_.*x_]]/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  1/b*Int[Sqrt[a+b*Cos[c+d*x]]/Sqrt[Cos[c+d*x]],x] - 
  a/b*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*Cos[c+d*x]*Sin[c+d*x]^(m-1)/(d*(2*m-1)*Sqrt[a+b*Sin[c+d*x]]) + 
  1/(b*(2*m-1))*Int[(Sin[c+d*x]^(m-2)*(2*b*(m-1)-a*Sin[c+d*x]))/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2


Int[cos[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*Sin[c+d*x]*Cos[c+d*x]^(m-1)/(d*(2*m-1)*Sqrt[a+b*Cos[c+d*x]]) + 
  1/(b*(2*m-1))*Int[(Cos[c+d*x]^(m-2)*(2*b*(m-1)-a*Cos[c+d*x]))/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2


Int[1/(sin[c_.+d_.*x_]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  1/a*Int[Sqrt[a+b*Sin[c+d*x]]/Sin[c+d*x],x] - 
  b/a*Int[1/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/(cos[c_.+d_.*x_]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  1/a*Int[Sqrt[a+b*Cos[c+d*x]]/Cos[c+d*x],x] - 
  b/a*Int[1/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Sin[c+d*x]]) + 
  1/(2*b*(m+1))*Int[(Sin[c+d*x]^(m+1)*(a+b*(2*m+3)*Sin[c+d*x]))/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Cos[c+d*x]]) + 
  1/(2*b*(m+1))*Int[(Cos[c+d*x]^(m+1)*(a+b*(2*m+3)*Cos[c+d*x]))/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(b*d*(2*n+1)*Sin[c+d*x]^(n+1)) + 
  (n+1)/(b*(2*n+1))*Int[(a+b*Sin[c+d*x])^(n+1)/Sin[c+d*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m+n+1==0


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(b*d*(2*n+1)*Cos[c+d*x]^(n+1)) + 
  (n+1)/(b*(2*n+1))*Int[(a+b*Cos[c+d*x])^(n+1)/Cos[c+d*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m+n+1==0


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(2*n+1)*Sin[c+d*x]^(n+1)) + 
  n/(a*(2*n+1))*Int[(a+b*Sin[c+d*x])^(n+1)/Sin[c+d*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m+n+2==0


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(d*(2*n+1)*Cos[c+d*x]^(n+1)) + 
  n/(a*(2*n+1))*Int[(a+b*Cos[c+d*x])^(n+1)/Cos[c+d*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m+n+2==0


Int[sin[c_.+d_.*x_]^2*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) - 
  1/(a^2*(2*n+1))*Int[(a*n-b*(2*n+1)*Sin[c+d*x])*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[cos[c_.+d_.*x_]^2*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(a*d*(2*n+1)) - 
  1/(a^2*(2*n+1))*Int[(a*n-b*(2*n+1)*Cos[c+d*x])*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*Sin[c+d*x]^(m-1)*(a+b*Sin[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Sin[c+d*x]^(m-2)*(a*(m-1)-b*(m-n-1)*Sin[c+d*x])*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m>1


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*Cos[c+d*x]^(m-1)*(a+b*Cos[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Cos[c+d*x]^(m-2)*(a*(m-1)-b*(m-n-1)*Cos[c+d*x])*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m>1


Int[Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cos[c+d*x]*Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^n/(b*d*(2*n+1)) - 
  1/(2*a*b*(2*n+1))*Int[(a-b*(2*n+3)*Sin[c+d*x])*(a+b*Sin[c+d*x])^(n+1)/Sqrt[Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sin[c+d*x]*Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^n/(b*d*(2*n+1)) - 
  1/(2*a*b*(2*n+1))*Int[(a-b*(2*n+3)*Cos[c+d*x])*(a+b*Cos[c+d*x])^(n+1)/Sqrt[Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Sin[c+d*x]^m*(a*(m+2*n+2)-b*(m+n+2)*Sin[c+d*x])*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2 && Not[RationalQ[m] && m>1]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Cos[c+d*x]^m*(a*(m+2*n+2)-b*(m+n+2)*Cos[c+d*x])*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2 && Not[RationalQ[m] && m>1]


Int[sin[c_.+d_.*x_]/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  1/b*Int[Sqrt[a+b*Sin[c+d*x]],x] - a/b*Int[1/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  1/b*Int[Sqrt[a+b*Cos[c+d*x]],x] - a/b*Int[1/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1)) + 
  n/(n+1)*Int[Simp[b+a*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(d*(n+1)) + 
  n/(n+1)*Int[Simp[b+a*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  1/((n+1)*(a^2-b^2))*Int[Simp[b*(n+1)-a*(n+2)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  1/((n+1)*(a^2-b^2))*Int[Simp[b*(n+1)-a*(n+2)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b*Int[(a+b*Sin[c+d*x])^(n+1),x] - 
  a/b*Int[(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b*Int[(a+b*Cos[c+d*x])^(n+1),x] - 
  a/b*Int[(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -a*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[(a+a*Sin[c+d*x]+b*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -a*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  Int[(a+a*Cos[c+d*x]+b*Cos[c+d*x]^2)/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*Cos[c+d*x]*Sin[c+d*x]^(m-1)*Sqrt[a+b*Sin[c+d*x]]/(d*(2*m+1)) + 
  1/(2*m+1)*Int[Sin[c+d*x]^(m-2)*Simp[2*a*(m-1)+b*(2*m-1)*Sin[c+d*x]+a*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[cos[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*Sin[c+d*x]*Cos[c+d*x]^(m-1)*Sqrt[a+b*Cos[c+d*x]]/(d*(2*m+1)) + 
  1/(2*m+1)*Int[Cos[c+d*x]^(m-2)*Simp[2*a*(m-1)+b*(2*m-1)*Cos[c+d*x]+a*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/sin[c_.+d_.*x_],x_Symbol] :=
  b*Int[1/Sqrt[a+b*Sin[c+d*x]],x] + 
  a*Int[1/(Sin[c+d*x]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/cos[c_.+d_.*x_],x_Symbol] :=
  b*Int[1/Sqrt[a+b*Cos[c+d*x]],x] + 
  a*Int[1/(Cos[c+d*x]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  (a-b)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] +
  b*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/Sqrt[cos[c_.+d_.*x_]],x_Symbol] :=
  (a-b)*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] +
  b*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
  (a+b)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  a*Int[(1-Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x] /; 
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/cos[c_.+d_.*x_]^(3/2),x_Symbol] :=
  (a+b)*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  a*Int[(1-Cos[c+d*x])/(Cos[c+d*x]^(3/2)*Sqrt[a+b*Cos[c+d*x]]),x] /; 
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]]/(d*(m+1)) + 
  1/(2*(m+1))*Int[Sin[c+d*x]^(m+1)*Simp[-b+2*a*(m+2)*Sin[c+d*x]+b*(2*m+5)*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-3/2 && IntegerQ[2*m]


Int[cos[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]]/(d*(m+1)) + 
  1/(2*(m+1))*Int[Cos[c+d*x]^(m+1)*Simp[-b+2*a*(m+2)*Cos[c+d*x]+b*(2*m+5)*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-3/2 && IntegerQ[2*m]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*b*Cos[c+d*x]*Sin[c+d*x]^m*Sqrt[a+b*Sin[c+d*x]]/(d*(2*m+3)) + 
  1/(2*m+3)*Int[Sin[c+d*x]^(m-1)*
    Simp[2*a*b*m+(a^2*(2*m+3)+b^2*(2*m+1))*Sin[c+d*x]+2*a*b*(m+2)*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[2*m]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^(3/2),x_Symbol] :=
  2*b*Sin[c+d*x]*Cos[c+d*x]^m*Sqrt[a+b*Cos[c+d*x]]/(d*(2*m+3)) + 
  1/(2*m+3)*Int[Cos[c+d*x]^(m-1)*
    Simp[2*a*b*m+(a^2*(2*m+3)+b^2*(2*m+1))*Cos[c+d*x]+2*a*b*(m+2)*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[2*m]


Int[(a_+b_.*sin[c_.+d_.*x_])^(3/2)/sin[c_.+d_.*x_],x_Symbol] :=
  b*Int[Sqrt[a+b*Sin[c+d*x]],x] + a*Int[Sqrt[a+b*Sin[c+d*x]]/Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*cos[c_.+d_.*x_])^(3/2)/cos[c_.+d_.*x_],x_Symbol] :=
  b*Int[Sqrt[a+b*Cos[c+d*x]],x] + a*Int[Sqrt[a+b*Cos[c+d*x]]/Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sin[c_.+d_.*x_])^(3/2)/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  3*a*b/2*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  1/2*Int[(a*(2*a-3*b)+a*b*Sin[c+d*x]+2*b^2*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*cos[c_.+d_.*x_])^(3/2)/Sqrt[cos[c_.+d_.*x_]],x_Symbol] :=
  3*a*b/2*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  1/2*Int[(a*(2*a-3*b)+a*b*Cos[c+d*x]+2*b^2*Cos[c+d*x]^2)/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sin[c_.+d_.*x_])^(3/2)/sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
  b^2*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[(a^2+b*(2*a-b)*Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*cos[c_.+d_.*x_])^(3/2)/cos[c_.+d_.*x_]^(3/2),x_Symbol] :=
  b^2*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  Int[(a^2+b*(2*a-b)*Cos[c+d*x])/(Cos[c+d*x]^(3/2)*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  a*Cos[c+d*x]*Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]]/(d*(m+1)) + 
  1/(2*(m+1))*Int[Sin[c+d*x]^(m+1)*
    Simp[a*b*(2*m+1)+2*(a^2*(m+2)+b^2*(m+1))*Sin[c+d*x]+a*b*(2*m+5)*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-3/2 && IntegerQ[2*m]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -a*Sin[c+d*x]*Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]]/(d*(m+1)) + 
  1/(2*(m+1))*Int[Cos[c+d*x]^(m+1)*
    Simp[a*b*(2*m+1)+2*(a^2*(m+2)+b^2*(m+1))*Cos[c+d*x]+a*b*(2*m+5)*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-3/2 && IntegerQ[2*m]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-2)/(d*(m+1)) + 
  1/(m+1)*
    Int[Sin[c+d*x]^(m+1)*
      Simp[a^2*b*(2*m-n+4)+a*(a^2*(m+2)+3*b^2*(m+1))*Sin[c+d*x]+b*(a^2*(m+n)+b^2*(m+1))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>2 && m<-1 && IntegersQ[2*m,2*n]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-2)/(d*(m+1)) + 
  1/(m+1)*
    Int[Cos[c+d*x]^(m+1)*
      Simp[a^2*b*(2*m-n+4)+a*(a^2*(m+2)+3*b^2*(m+1))*Cos[c+d*x]+b*(a^2*(m+n)+b^2*(m+1))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>2 && m<-1 && IntegersQ[2*m,2*n]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-2)/(d*(m+n)) + 
  1/(m+n)*
    Int[Sin[c+d*x]^m*
      Simp[a*(b^2*(m+1)+a^2*(m+n))+b*(b^2*(m+n-1)+3*a^2*(m+n))*Sin[c+d*x]+a*b^2*(2*m+3*n+-2)*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>2 && m>=-1 && IntegersQ[2*m,2*n]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-2)/(d*(m+n)) + 
  1/(m+n)*
    Int[Cos[c+d*x]^m*
      Simp[a*(b^2*(m+1)+a^2*(m+n))+b*(b^2*(m+n-1)+3*a^2*(m+n))*Cos[c+d*x]+a*b^2*(2*m+3*n+-2)*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>2 && m>=-1 && IntegersQ[2*m,2*n]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[Sin[c+d*x]^m,(a+b*Sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[Cos[c+d*x]^m,(a+b*Cos[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[n]


Int[Sqrt[sin[c_.+d_.*x_]]/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] +
  Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[cos[c_.+d_.*x_]]/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] +
  Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -a/(2*b)*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  1/(2*b)*Int[(a+a*Sin[c+d*x]+2*b*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -a/(2*b)*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  1/(2*b)*Int[(a+a*Cos[c+d*x]+2*b*Cos[c+d*x]^2)/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*Cos[c+d*x]*Sin[c+d*x]^(m-2)*Sqrt[a+b*Sin[c+d*x]]/(b*d*(2*m-1)) + 
  1/(b*(2*m-1))*Int[Sin[c+d*x]^(m-3)*Simp[2*a*(m-2)+b*(2*m-3)*Sin[c+d*x]-2*a*(m-1)*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>=2 && IntegerQ[2*m]


Int[cos[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*Sin[c+d*x]*Cos[c+d*x]^(m-2)*Sqrt[a+b*Cos[c+d*x]]/(b*d*(2*m-1)) + 
  1/(b*(2*m-1))*Int[Cos[c+d*x]^(m-3)*Simp[2*a*(m-2)+b*(2*m-3)*Cos[c+d*x]-2*a*(m-1)*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>=2 && IntegerQ[2*m]


Int[1/(sin[c_.+d_.*x_]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  2/(d*Rt[a+b,2])*EllipticPi[2,(c+d*x)/2-Pi/4,2*b/(a+b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]


Int[1/(cos[c_.+d_.*x_]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  2/(d*Rt[a+b,2])*EllipticPi[2,(c+d*x)/2,2*b/(a+b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]


Int[1/(sin[c_.+d_.*x_]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  -2/(d*Rt[a-b,2])*EllipticPi[2,Pi/4+(c+d*x)/2,-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a-b]


Int[1/(cos[c_.+d_.*x_]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  2/(d*Rt[a-b,2])*EllipticPi[2,Pi/2-(c+d*x)/2,-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a-b]


Int[1/(sin[c_.+d_.*x_]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  Sqrt[(a+b*Sin[c+d*x])/(a+b)]/Sqrt[a+b*Sin[c+d*x]]*Int[1/(Sin[c+d*x]*Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[1/(cos[c_.+d_.*x_]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  Sqrt[(a+b*Cos[c+d*x])/(a+b)]/Sqrt[a+b*Cos[c+d*x]]*Int[1/(Cos[c+d*x]*Sqrt[a/(a+b)+b/(a+b)*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[1/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  -2/(d*Sqrt[a+b])*EllipticF[ArcSin[Cos[c+d*x]/(1+Sin[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d},x] && PositiveQ[b] && PositiveQ[b^2-a^2]


Int[1/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  2/(d*Sqrt[a+b])*EllipticF[ArcSin[Sin[c+d*x]/(1+Cos[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d},x] && PositiveQ[b] && PositiveQ[b^2-a^2]


Int[1/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  -2*Sqrt[1+Sin[c+d*x]]/(d*Sqrt[a+b*Sin[c+d*x]])*
    Sqrt[(a+b*Sin[c+d*x])/((a+b)*(1+Sin[c+d*x]))]*
    EllipticF[ArcSin[Cos[c+d*x]/(1+Sin[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  2*Sqrt[1+Cos[c+d*x]]/(d*Sqrt[a+b*Cos[c+d*x]])*
    Sqrt[(a+b*Cos[c+d*x])/((a+b)*(1+Cos[c+d*x]))]*
    EllipticF[ArcSin[Sin[c+d*x]/(1+Cos[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[(1-Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(cos[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  Int[(1-Cos[c+d*x])/(Cos[c+d*x]^(3/2)*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*Int[Sin[c+d*x]^(m+1)*Simp[-b*(2*m+3)+2*a*(m+2)*Sin[c+d*x]+b*(2*m+5)*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-3/2 && IntegerQ[2*m]


Int[cos[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*Int[Cos[c+d*x]^(m+1)*Simp[-b*(2*m+3)+2*a*(m+2)*Cos[c+d*x]+b*(2*m+5)*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-3/2 && IntegerQ[2*m]


Int[Sqrt[sin[c_.+d_.*x_]]/(a_+b_.*sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -1/(a-b)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  a/(a-b)*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x] /; 
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[cos[c_.+d_.*x_]]/(a_+b_.*cos[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -1/(a-b)*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  a/(a-b)*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(3/2)),x] /; 
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/(2*(n+1)*(a^2-b^2))*Int[Simp[b+2*a*(n+1)*Sin[c+d*x]-b*(2*n+5)*Sin[c+d*x]^2,x]*(a+b*Sin[c+d*x])^(n+1)/Sqrt[Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-3/2 && IntegerQ[2*n]


Int[Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]*Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/(2*(n+1)*(a^2-b^2))*Int[Simp[b+2*a*(n+1)*Cos[c+d*x]-b*(2*n+5)*Cos[c+d*x]^2,x]*(a+b*Cos[c+d*x])^(n+1)/Sqrt[Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-3/2 && IntegerQ[2*n]


Int[sin[c_.+d_.*x_]^(3/2)/(a_+b_.*sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  1/b*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] - 
  1/b*Int[(a+(a+b)*Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^(3/2)/(a_+b_.*cos[c_.+d_.*x_])^(3/2),x_Symbol] :=
  1/b*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] - 
  1/b*Int[(a+(a+b)*Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^(3/2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cos[c+d*x]*Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  1/(2*(n+1)*(a^2-b^2))*Int[Simp[a+2*b*(n+1)*Sin[c+d*x]-a*(2*n+5)*Sin[c+d*x]^2,x]*(a+b*Sin[c+d*x])^(n+1)/Sqrt[Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-3/2 && IntegerQ[2*n]


Int[cos[c_.+d_.*x_]^(3/2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sin[c+d*x]*Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  1/(2*(n+1)*(a^2-b^2))*Int[Simp[a+2*b*(n+1)*Cos[c+d*x]-a*(2*n+5)*Cos[c+d*x]^2,x]*(a+b*Cos[c+d*x])^(n+1)/Sqrt[Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-3/2 && IntegerQ[2*n]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Cos[c+d*x]*Sin[c+d*x]^(m-2)*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sin[c+d*x]^(m-3)*
      Simp[a^2*(m-2)+a*b*(n+1)*Sin[c+d*x]-(b^2*(n+1)+a^2*(m-1))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>=2 && IntegersQ[2*m,2*n]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Sin[c+d*x]*Cos[c+d*x]^(m-2)*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Cos[c+d*x]^(m-3)*
      Simp[a^2*(m-2)+a*b*(n+1)*Cos[c+d*x]-(b^2*(n+1)+a^2*(m-1))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>=2 && IntegersQ[2*m,2*n]


Int[1/(Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  1/(a-b)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] - 
  b/(a-b)*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  1/(a-b)*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] - 
  b/(a-b)*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Sin[c+d*x]^m*
      Simp[a^2*(n+1)-b^2*(m+n+2)-a*b*(n+1)*Sin[c+d*x]+b^2*(m+n+3)*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m<0 && IntegersQ[2*m,2*n]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Cos[c+d*x]^m*
      Simp[a^2*(n+1)-b^2*(m+n+2)-a*b*(n+1)*Cos[c+d*x]+b^2*(m+n+3)*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m<0 && IntegersQ[2*m,2*n]


Int[sin[c_.+d_.*x_]^2*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Simp[b*(n+1)-a*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[cos[c_.+d_.*x_]^2*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Simp[b*(n+1)-a*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b*Int[Sin[c+d*x]^(m-1)*(a+b*Sin[c+d*x])^(n+1),x] - 
  a/b*Int[Sin[c+d*x]^(m-1)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b*Int[Cos[c+d*x]^(m-1)*(a+b*Cos[c+d*x])^(n+1),x] - 
  a/b*Int[Cos[c+d*x]^(m-1)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m]


Int[sin[c_.+d_.*x_]^m_.*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Sin[c+d*x]^m*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[cos[c_.+d_.*x_]^m_.*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Cos[c+d*x]^m*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


(* ::Subsection::Closed:: *)
(*7.1.2 sin(c+d x)^m (A+B sin(c+d x)) (a+b sin(c+d x))^n*)


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_])*(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Sin[c+d*x])*(b*Sin[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,n},x] && IntegerQ[m]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_])*(b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Cos[c+d*x])*(b*Cos[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,n},x] && IntegerQ[m]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(b_*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Sin[c+d*x]]/Sqrt[Sin[c+d*x]]*Int[Sin[c+d*x]^(m+n)*(A+B*Sin[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(b_*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Cos[c+d*x]]/Sqrt[Cos[c+d*x]]*Int[Cos[c+d*x]^(m+n)*(A+B*Cos[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(b_*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Sin[c+d*x]]/Sqrt[b*Sin[c+d*x]]*Int[Sin[c+d*x]^(m+n)*(A+B*Sin[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(b_*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Cos[c+d*x]]/Sqrt[b*Cos[c+d*x]]*Int[Cos[c+d*x]^(m+n)*(A+B*Cos[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Sin[c+d*x])^n/Sin[c+d*x]^n*Int[Sin[c+d*x]^(m+n)*(A+B*Sin[c+d*x]),x] /;
FreeQ[{b,c,d,A,B,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cos[c+d*x])^n/Cos[c+d*x]^n*Int[Cos[c+d*x]^(m+n)*(A+B*Cos[c+d*x]),x] /;
FreeQ[{b,c,d,A,B,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[Sin[c+d*x]^m*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[A*b-a*B]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[Cos[c+d*x]^m*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[A*b-a*B]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  a*A*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(m+1)) + 
  1/(m+1)*Int[Sin[c+d*x]^(m+1)*Simp[(A*b+a*B)*(m+1)+(a*A*(m+2)+b*B*(m+1))*Sin[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -a*A*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(m+1)) + 
  1/(m+1)*Int[Cos[c+d*x]^(m+1)*Simp[(A*b+a*B)*(m+1)+(a*A*(m+2)+b*B*(m+1))*Cos[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -b*B*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(m+2)) + 
  1/(m+2)*Int[Sin[c+d*x]^m*Simp[a*A*(m+2)+b*B*(m+1)+(A*b+a*B)*(m+2)*Sin[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  b*B*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(m+2)) + 
  1/(m+2)*Int[Cos[c+d*x]^m*Simp[a*A*(m+2)+b*B*(m+1)+(A*b+a*B)*(m+2)*Cos[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B]


Int[sin[c_.+d_.*x_]*(A_+B_.*sin[c_.+d_.*x_])/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -B*Cos[c+d*x]/(b*d) + 
  (A*b-a*B)/b*Int[Sin[c+d*x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[cos[c_.+d_.*x_]*(A_+B_.*cos[c_.+d_.*x_])/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  B*Sin[c+d*x]/(b*d) + 
  (A*b-a*B)/b*Int[Cos[c+d*x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[sin[c_.+d_.*x_]*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a*A-b*B)*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[n*(A*b-a*B)+b*B*(2*n+1)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (a*A-b*B)*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(a*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[n*(A*b-a*B)+b*B*(2*n+1)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(A*b-a*B)*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) - 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Simp[b*(n+1)*(A*b-a*B)+(a^2*B-a*A*b*(n+2)+b^2*B*(n+1))*Sin[c+d*x],x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(A*b-a*B)*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) - 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Simp[b*(n+1)*(A*b-a*B)+(a^2*B-a*A*b*(n+2)+b^2*B*(n+1))*Cos[c+d*x],x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Simp[b*B*(n+1)-(a*B-A*b*(n+2))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B]


Int[cos[c_.+d_.*x_]*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  B*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Simp[b*B*(n+1)-(a*B-A*b*(n+2))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(n+1)) /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+2] && ZeroQ[A*b*n+a*B*(n+1)]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(n+1)) /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+2] && ZeroQ[A*b*n+a*B*(n+1)]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(b*d*(2*n+1)) + 
  (A*b*n+a*B*(n+1))/(a*b*(2*n+1))*Int[Sin[c+d*x]^m*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+2] && NonzeroQ[A*b*n+a*B*(n+1)] && RationalQ[n] && n<=-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(b*d*(2*n+1)) + 
  (A*b*n+a*B*(n+1))/(a*b*(2*n+1))*Int[Cos[c+d*x]^m*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+2] && NonzeroQ[A*b*n+a*B*(n+1)] && RationalQ[n] && n<=-1


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(n+1)) + 
  (A*b*n+a*B*(n+1))/(a*(n+1))*Int[Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+2] && NonzeroQ[A*b*n+a*B*(n+1)]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(n+1)) + 
  (A*b*n+a*B*(n+1))/(a*(n+1))*Int[Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+2] && NonzeroQ[A*b*n+a*B*(n+1)]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  a*A*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Sin[c+d*x]]) /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[2*a*B*(m+1)+A*b*(2*m+3)]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -a*A*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Cos[c+d*x]]) /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[2*a*B*(m+1)+A*b*(2*m+3)]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  a*A*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Sin[c+d*x]]) + 
  (2*a*B*(m+1)+A*b*(2*m+3))/(2*a*(m+1))*Int[Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[2*a*B*(m+1)+A*b*(2*m+3)] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -a*A*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Cos[c+d*x]]) + 
  (2*a*B*(m+1)+A*b*(2*m+3))/(2*a*(m+1))*Int[Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[2*a*B*(m+1)+A*b*(2*m+3)] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*b*B*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(2*m+3)*Sqrt[a+b*Sin[c+d*x]]) + 
  (2*a*B*(m+1)+A*b*(2*m+3))/(b*(2*m+3))*Int[Sin[c+d*x]^m*Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[2*a*B*(m+1)+A*b*(2*m+3)]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*b*B*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(2*m+3)*Sqrt[a+b*Cos[c+d*x]]) + 
  (2*a*B*(m+1)+A*b*(2*m+3))/(b*(2*m+3))*Int[Cos[c+d*x]^m*Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[2*a*B*(m+1)+A*b*(2*m+3)]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-1)/(d*(m+1)) + 
  1/(m+1)*
    Int[Sin[c+d*x]^(m+1)*Simp[a*B*(m+1)+A*b*(m-n+2)+(b*B*(m+1)+a*A*(m+n+1))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1/2 && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-1)/(d*(m+1)) + 
  1/(m+1)*
    Int[Cos[c+d*x]^(m+1)*Simp[a*B*(m+1)+A*b*(m-n+2)+(b*B*(m+1)+a*A*(m+n+1))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1/2 && m<-1


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*B*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-1)/(d*(m+n+1)) + 
  1/(m+n+1)*
    Int[Sin[c+d*x]^m*Simp[b*B*(m+1)+a*A*(m+n+1)+(A*b*(m+n+1)+a*B*(m+2*n))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2 && Not[RationalQ[m] && m<-1]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*B*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-1)/(d*(m+n+1)) + 
  1/(m+n+1)*
    Int[Cos[c+d*x]^m*Simp[b*B*(m+1)+a*A*(m+n+1)+(A*b*(m+n+1)+a*B*(m+2*n))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2 && Not[RationalQ[m] && m<-1]


Int[(A_+B_.*sin[c_.+d_.*x_])/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  B/b*Int[Sqrt[a+b*Sin[c+d*x]]/Sqrt[Sin[c+d*x]],x] + 
  (A*b-a*B)/b*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  B/b*Int[Sqrt[a+b*Cos[c+d*x]]/Sqrt[Cos[c+d*x]],x] + 
  (A*b-a*B)/b*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cos[c+d*x]*Sin[c+d*x]^m/(d*(2*m+1)*Sqrt[a+b*Sin[c+d*x]]) + 
  1/(a*(2*m+1))*
    Int[Sin[c+d*x]^(m-1)*Simp[2*a*B*m-(b*B-a*A*(2*m+1))*Sin[c+d*x],x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*B*Sin[c+d*x]*Cos[c+d*x]^m/(d*(2*m+1)*Sqrt[a+b*Cos[c+d*x]]) + 
  1/(a*(2*m+1))*
    Int[Cos[c+d*x]^(m-1)*Simp[2*a*B*m-(b*B-a*A*(2*m+1))*Cos[c+d*x],x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(A_+B_.*sin[c_.+d_.*x_])/(sin[c_.+d_.*x_]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Sin[c+d*x]]/Sin[c+d*x],x] - 
  (A*b-a*B)/a*Int[1/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])/(cos[c_.+d_.*x_]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Cos[c+d*x]]/Cos[c+d*x],x] - 
  (A*b-a*B)/a*Int[1/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Sin[c+d*x]]) + 
  1/(2*a*(m+1))*
    Int[Sin[c+d*x]^(m+1)*Simp[2*a*B*(m+1)+A*b+a*A*(2*m+3)*Sin[c+d*x],x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Cos[c+d*x]]) + 
  1/(2*a*(m+1))*
    Int[Cos[c+d*x]^(m+1)*Simp[2*a*B*(m+1)+A*b+a*A*(2*m+3)*Cos[c+d*x],x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Cos[c+d*x]*Sin[c+d*x]^m*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) - 
  1/(a^2*(2*n+1))*
    Int[Sin[c+d*x]^(m-1)*Simp[m*(A*b-a*B)+(b*B*(m-n)-a*A*(m+n+1))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<=-1/2 && m>0


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Sin[c+d*x]*Cos[c+d*x]^m*(a+b*Cos[c+d*x])^n/(a*d*(2*n+1)) - 
  1/(a^2*(2*n+1))*
    Int[Cos[c+d*x]^(m-1)*Simp[m*(A*b-a*B)+(b*B*(m-n)-a*A*(m+n+1))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<=-1/2 && m>0


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(b^2*(2*n+1))*
    Int[Sin[c+d*x]^m*Simp[(a*A-b*B)*(m+1)+a*A*(2*n+1)-(A*b-a*B)*(m+n+2)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1/2 && Not[RationalQ[m] && m>0]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(b^2*(2*n+1))*
    Int[Cos[c+d*x]^m*Simp[(a*A-b*B)*(m+1)+a*A*(2*n+1)-(A*b-a*B)*(m+n+2)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1/2 && Not[RationalQ[m] && m>0]


Int[(A_+B_.*sin[c_.+d_.*x_])*Sqrt[a_+b_.*sin[c_.+d_.*x_]]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  1/2*Int[Simp[a*(2*A-B)+(2*A*b+a*B)*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  B/2*Int[Simp[a+a*Sin[c+d*x]+2*b*Sin[c+d*x]^2,x]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])*Sqrt[a_+b_.*cos[c_.+d_.*x_]]/Sqrt[cos[c_.+d_.*x_]],x_Symbol] :=
  1/2*Int[Simp[a*(2*A-B)+(2*A*b+a*B)*Cos[c+d*x],x]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  B/2*Int[Simp[a+a*Cos[c+d*x]+2*b*Cos[c+d*x]^2,x]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cos[c+d*x]*Sin[c+d*x]^m*Sqrt[a+b*Sin[c+d*x]]/(d*(2*m+3)) + 
  1/(2*m+3)*
    Int[Sin[c+d*x]^(m-1)*
      Simp[2*a*B*m+(b*B*(2*m+1)+a*A*(2*m+3))*Sin[c+d*x]+(a*B+A*b*(2*m+3))*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*B*Sin[c+d*x]*Cos[c+d*x]^m*Sqrt[a+b*Cos[c+d*x]]/(d*(2*m+3)) + 
  1/(2*m+3)*
    Int[Cos[c+d*x]^(m-1)*
      Simp[2*a*B*m+(b*B*(2*m+1)+a*A*(2*m+3))*Cos[c+d*x]+(a*B+A*b*(2*m+3))*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(A_+B_.*sin[c_.+d_.*x_])*Sqrt[a_+b_.*sin[c_.+d_.*x_]]/sin[c_.+d_.*x_],x_Symbol] :=
  B*Int[Sqrt[a+b*Sin[c+d*x]],x] + 
  A*Int[Sqrt[a+b*Sin[c+d*x]]/Sin[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])*Sqrt[a_+b_.*cos[c_.+d_.*x_]]/cos[c_.+d_.*x_],x_Symbol] :=
  B*Int[Sqrt[a+b*Cos[c+d*x]],x] + 
  A*Int[Sqrt[a+b*Cos[c+d*x]]/Cos[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_])*Sqrt[a_+b_.*sin[c_.+d_.*x_]]/sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
  (b*(A-B)+a*(A+B))*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[Simp[a*A-(a*A-b*B)*Sin[c+d*x]+b*B*Sin[c+d*x]^2,x]/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])*Sqrt[a_+b_.*cos[c_.+d_.*x_]]/cos[c_.+d_.*x_]^(3/2),x_Symbol] :=
  (b*(A-B)+a*(A+B))*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  Int[Simp[a*A-(a*A-b*B)*Cos[c+d*x]+b*B*Cos[c+d*x]^2,x]/(Cos[c+d*x]^(3/2)*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]]/(d*(m+1)) + 
  1/(2*(m+1))*
    Int[Sin[c+d*x]^(m+1)*
      Simp[2*a*B*(m+1)-A*b+2*(a*A+(a*A+b*B)*(m+1))*Sin[c+d*x]+A*b*(2*m+5)*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]]/(d*(m+1)) + 
  1/(2*(m+1))*
    Int[Cos[c+d*x]^(m+1)*
      Simp[2*a*B*(m+1)-A*b+2*(a*A+(a*A+b*B)*(m+1))*Cos[c+d*x]+A*b*(2*m+5)*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-1)/(d*(m+1)) + 
  1/(m+1)*
    Int[Sin[c+d*x]^(m+1)*
      Simp[a*(a*B*(m+1)+A*b*(m-n+2))+(b*(A*b+2*a*B)*(m+1)+a^2*A*(m+2))*Sin[c+d*x]+b*(b*B*(m+1)+a*A*(m+n+1))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-1)/(d*(m+1)) + 
  1/(m+1)*
    Int[Cos[c+d*x]^(m+1)*
      Simp[a*(a*B*(m+1)+A*b*(m-n+2))+(b*(A*b+2*a*B)*(m+1)+a^2*A*(m+2))*Cos[c+d*x]+b*(b*B*(m+1)+a*A*(m+n+1))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*B*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-1)/(d*(m+n+1)) + 
  1/(m+n+1)*
    Int[Sin[c+d*x]^m*
      Simp[a*(b*B*(m+1)+a*A*(m+n+1))+(b^2*B*(m+n)+a*(2*A*b+a*B)*(m+n+1))*Sin[c+d*x]+b*(A*b*(m+n+1)+a*B*(m+2*n))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*B*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-1)/(d*(m+n+1)) + 
  1/(m+n+1)*
    Int[Cos[c+d*x]^m*
      Simp[a*(b*B*(m+1)+a*A*(m+n+1))+(b^2*B*(m+n)+a*(2*A*b+a*B)*(m+n+1))*Cos[c+d*x]+b*(A*b*(m+n+1)+a*B*(m+2*n))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -B*Cos[c+d*x]*Sin[c+d*x]^(m-1)/(b*d*m) + 
  1/(b*m)*
    Int[Sin[c+d*x]^(m-2)*Simp[a*B*(m-1)+b*B*(m-1)*Sin[c+d*x]+m*(A*b-a*B)*Sin[c+d*x]^2,x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  B*Sin[c+d*x]*Cos[c+d*x]^(m-1)/(b*d*m) + 
  1/(b*m)*
    Int[Cos[c+d*x]^(m-2)*Simp[a*B*(m-1)+b*B*(m-1)*Cos[c+d*x]+m*(A*b-a*B)*Cos[c+d*x]^2,x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[(A_+B_.*sin[c_.+d_.*x_])/(sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Sin[c+d*x],x] - 
  (A*b-a*B)/a*Int[1/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])/(cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Cos[c+d*x],x] - 
  (A*b-a*B)/a*Int[1/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(a*d*(m+1)) + 
  1/(a*(m+1))*
    Int[Sin[c+d*x]^(m+1)*Simp[(a*B-A*b)*(m+1)+a*A*(m+2)*Sin[c+d*x]+A*b*(m+2)*Sin[c+d*x]^2,x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(a*d*(m+1)) + 
  1/(a*(m+1))*
    Int[Cos[c+d*x]^(m+1)*Simp[(a*B-A*b)*(m+1)+a*A*(m+2)*Cos[c+d*x]+A*b*(m+2)*Cos[c+d*x]^2,x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  B/b*Int[Sin[c+d*x]^m,x] + (A*b-a*B)/b*Int[Sin[c+d*x]^m/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  B/b*Int[Cos[c+d*x]^m,x] + (A*b-a*B)/b*Int[Cos[c+d*x]^m/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[sin[c_.+d_.*x_]]*(A_+B_.*sin[c_.+d_.*x_])/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  1/(2*b)*Int[Simp[-a*B+(2*A*b-a*B)*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  B/(2*b)*Int[Simp[a+a*Sin[c+d*x]+2*b*Sin[c+d*x]^2,x]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[cos[c_.+d_.*x_]]*(A_+B_.*cos[c_.+d_.*x_])/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  1/(2*b)*Int[Simp[-a*B+(2*A*b-a*B)*Cos[c+d*x],x]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  B/(2*b)*Int[Simp[a+a*Cos[c+d*x]+2*b*Cos[c+d*x]^2,x]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cos[c+d*x]*Sin[c+d*x]^(m-1)*Sqrt[a+b*Sin[c+d*x]]/(b*d*(2*m+1)) + 
  1/(b*(2*m+1))*
    Int[Sin[c+d*x]^(m-2)*Simp[2*a*B*(m-1)+b*B*(2*m-1)*Sin[c+d*x]-(2*a*B*m-A*(b+2*b*m))*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*B*Sin[c+d*x]*Cos[c+d*x]^(m-1)*Sqrt[a+b*Cos[c+d*x]]/(b*d*(2*m+1)) + 
  1/(b*(2*m+1))*
    Int[Cos[c+d*x]^(m-2)*Simp[2*a*B*(m-1)+b*B*(2*m-1)*Cos[c+d*x]-(2*a*B*m-A*(b+2*b*m))*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[(A_+B_.*sin[c_.+d_.*x_])/(sin[c_.+d_.*x_]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  B*Int[1/Sqrt[a+b*Sin[c+d*x]],x] + 
  A*Int[1/(Sin[c+d*x]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])/(cos[c_.+d_.*x_]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  B*Int[1/Sqrt[a+b*Cos[c+d*x]],x] + 
  A*Int[1/(Cos[c+d*x]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_])/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  4*A/(d*Sqrt[a+b])*EllipticPi[-1,-ArcSin[Cos[c+d*x]/(1+Sin[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && PositiveQ[b] && PositiveQ[b^2-a^2]


Int[(A_+B_.*cos[c_.+d_.*x_])/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  4*A/(d*Sqrt[a+b])*EllipticPi[-1,ArcSin[Sin[c+d*x]/(1+Cos[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && PositiveQ[b] && PositiveQ[b^2-a^2]


Int[(A_+B_.*sin[c_.+d_.*x_])/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  4*A*Sqrt[1+Sin[c+d*x]]/(d*Sqrt[a+b*Sin[c+d*x]])*
    Sqrt[(a+b*Sin[c+d*x])/((a+b)*(1+Sin[c+d*x]))]*
    EllipticPi[-1,-ArcSin[Cos[c+d*x]/(1+Sin[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_])/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  4*A*Sqrt[1+Cos[c+d*x]]/(d*Sqrt[a+b*Cos[c+d*x]])*
    Sqrt[(a+b*Cos[c+d*x])/((a+b)*(1+Cos[c+d*x]))]*
    EllipticPi[-1,ArcSin[Sin[c+d*x]/(1+Cos[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_])/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  B*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  (A-B)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]


Int[(A_+B_.*cos[c_.+d_.*x_])/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  B*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  (A-B)*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]


Int[(A_+B_.*sin[c_.+d_.*x_])/(sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  -2*A*Cos[c+d*x]*Sqrt[a+b*Sin[c+d*x]]/(a*d*Sqrt[Sin[c+d*x]]*(1+Sin[c+d*x])) - 
  2*A/a*Int[Sqrt[a+b*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(1+Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A+B]


Int[(A_+B_.*cos[c_.+d_.*x_])/(cos[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  2*A*Sin[c+d*x]*Sqrt[a+b*Cos[c+d*x]]/(a*d*Sqrt[Cos[c+d*x]]*(1+Cos[c+d*x])) - 
  2*A/a*Int[Sqrt[a+b*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*(1+Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A+B]


Int[(A_+B_.*sin[c_.+d_.*x_])/(sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  (A+B)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  A*Int[(1-Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[A+B]


Int[(A_+B_.*cos[c_.+d_.*x_])/(cos[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  (A+B)*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  A*Int[(1-Cos[c+d*x])/(Cos[c+d*x]^(3/2)*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[A+B]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*
    Int[Sin[c+d*x]^(m+1)*Simp[2*(a*B-A*b)*(m+1)-A*b+2*a*A*(m+2)*Sin[c+d*x]+A*b*(2*m+5)*Sin[c+d*x]^2,x]/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-3/2


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*
    Int[Cos[c+d*x]^(m+1)*Simp[2*(a*B-A*b)*(m+1)-A*b+2*a*A*(m+2)*Cos[c+d*x]+A*b*(2*m+5)*Cos[c+d*x]^2,x]/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && m!=-3/2


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(A*b-a*B)*Cos[c+d*x]*Sin[c+d*x]^(m-1)*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) - 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sin[c+d*x]^(m-2)*
      Simp[a*(A*b-a*B)*(m-1)+b*(A*b-a*B)*(n+1)*Sin[c+d*x]-
        (b*(a*A-b*B)*(n+1)+a*m*(A*b-a*B))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(A*b-a*B)*Sin[c+d*x]*Cos[c+d*x]^(m-1)*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) - 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Cos[c+d*x]^(m-2)*
      Simp[a*(A*b-a*B)*(m-1)+b*(A*b-a*B)*(n+1)*Cos[c+d*x]-
        (b*(a*A-b*B)*(n+1)+a*m*(A*b-a*B))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>1


Int[Sqrt[sin[c_.+d_.*x_]]*(A_+B_.*sin[c_.+d_.*x_])/(a_+b_.*sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  B/b*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  1/b*Int[Simp[-a*B+(A*b-(a+b)*B)*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[cos[c_.+d_.*x_]]*(A_+B_.*cos[c_.+d_.*x_])/(a_+b_.*cos[c_.+d_.*x_])^(3/2),x_Symbol] :=
  B/b*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  1/b*Int[Simp[-a*B+(A*b-(a+b)*B)*Cos[c+d*x],x]/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[sin[c_.+d_.*x_]]*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cos[c+d*x]*Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/(2*(n+1)*(a^2-b^2))*
    Int[Simp[A*b-a*B+2*(a*A-b*B)*(n+1)*Sin[c+d*x]-(A*b-a*B)*(2*n+5)*Sin[c+d*x]^2,x]*(a+b*Sin[c+d*x])^(n+1)/Sqrt[Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[Sqrt[cos[c_.+d_.*x_]]*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Sin[c+d*x]*Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/(2*(n+1)*(a^2-b^2))*
    Int[Simp[A*b-a*B+2*(a*A-b*B)*(n+1)*Cos[c+d*x]-(A*b-a*B)*(2*n+5)*Cos[c+d*x]^2,x]*(a+b*Cos[c+d*x])^(n+1)/Sqrt[Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*sin[c_.+d_.*x_])/(Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  -2*A*(a-b)*Cos[c+d x]*Sqrt[Sin[c+d*x]]/(a*d*(a+b)*Sqrt[a+b*Sin[c+d*x]]*(1+Sin[c+d x])) + 
  2*A/(a*(a+b))*Int[Sqrt[a+b*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(1+Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B]


Int[(A_+B_.*cos[c_.+d_.*x_])/(Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  2*A*(a-b)*Sin[c+d x]*Sqrt[Cos[c+d*x]]/(a*d*(a+b)*Sqrt[a+b*Cos[c+d*x]]*(1+Cos[c+d x])) + 
  2*A/(a*(a+b))*Int[Sqrt[a+b*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*(1+Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B]


Int[(A_+B_.*sin[c_.+d_.*x_])/(Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  (A-B)/(a-b)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] - 
  (A*b-a*B)/(a-b)*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]


Int[(A_+B_.*cos[c_.+d_.*x_])/(Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  (A-B)/(a-b)*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] - 
  (A*b-a*B)/(a-b)*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(A*b-a*B)*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Sin[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-b*(A*b-a*B)*(m+1)-a*(A*b-a*B)*(n+1)*Sin[c+d*x]+
        b*(A*b-a*B)*(m+n+3)*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>1]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(A*b-a*B)*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Cos[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-b*(A*b-a*B)*(m+1)-a*(A*b-a*B)*(n+1)*Cos[c+d*x]+
        b*(A*b-a*B)*(m+n+3)*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>1]


(* Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_])*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Sin[c+d*x]^m*(a+b*Sin[c+d*x])^n,x] + B*Int[Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] *)


(* Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_])*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Cos[c+d*x]^m*(a+b*Cos[c+d*x])^n,x] + B*Int[Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] *)


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_])*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Sin[c+d*x]^m*(A+B*Sin[c+d*x])*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_])*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Cos[c+d*x]^m*(A+B*Cos[c+d*x])*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x]


Int[(e_*sin[c_.+d_.*x_])^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m/Sin[c+d*x]^m*Int[Sin[c+d*x]^m*(A+B*Sin[c+d*x])*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_*cos[c_.+d_.*x_])^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m/Cos[c+d*x]^m*Int[Cos[c+d*x]^m*(A+B*Cos[c+d*x])*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*csc[c_.+d_.*x_])^m_*(A_+B_.*sin[c_.+d_.*x_])*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m*Sin[c+d*x]^m*Int[(A+B*Sin[c+d*x])*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*sec[c_.+d_.*x_])^m_*(A_+B_.*cos[c_.+d_.*x_])*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m*Cos[c+d*x]^m*Int[(A+B*Cos[c+d*x])*(a+b*Cos[c+d*x])^n/Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*csc[c_.+d_.*x_])^m_.*(f_.*sin[c_.+d_.*x_])^p_.*(A_.+B_.*sin[c_.+d_.*x_])*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m*(f*Sin[c+d*x])^p/Sin[c+d*x]^(p-m)*Int[Sin[c+d*x]^(p-m)*(A+B*Sin[c+d*x])*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x]


Int[(e_.*sec[c_.+d_.*x_])^m_.*(f_.*cos[c_.+d_.*x_])^p_.*(A_.+B_.*cos[c_.+d_.*x_])*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m*(f*Cos[c+d*x])^p/Cos[c+d*x]^(p-m)*Int[Cos[c+d*x]^(p-m)*(A+B*Cos[c+d*x])*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x]


Int[u_.*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Sin[c+d*x])*(a+b*Sin[c+d*x])^n/Sin[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B,n},x]


Int[u_.*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Cos[c+d*x])*(a+b*Cos[c+d*x])^n/Cos[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B,n},x]


(* ::Subsection::Closed:: *)
(*7.1.3 sin(c+d x)^m (A+B sin(c+d x)+C sin(c+d x)^2) (a+b sin(c+d x))^n*)


Int[(B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sin[c+d*x]*(B+C*Sin[c+d*x])*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,n},x]


Int[(B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cos[c+d*x]*(B+C*Cos[c+d*x])*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,n},x]


Int[sin[c_.+d_.*x_]^m_.*(B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sin[c+d*x]^(m+1)*(B+C*Sin[c+d*x])*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,m,n},x]


Int[cos[c_.+d_.*x_]^m_.*(B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cos[c+d*x]^(m+1)*(B+C*Cos[c+d*x])*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,m,n},x]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)*(b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Cos[c+d*x]*(b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{b,c,d,A,C,n},x] && ZeroQ[C*(n+1)+A*(n+2)]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)*(b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  -A*Sin[c+d*x]*(b*Cos[c+d*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{b,c,d,A,C,n},x] && ZeroQ[C*(n+1)+A*(n+2)]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)*(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*(b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) + 
  (C*(n+1)+A*(n+2))/(b^2*(n+1))*Int[(b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{b,c,d,A,C},x] && NonzeroQ[C*(n+1)+A*(n+2)] && RationalQ[n] && n<-1


Int[(A_+C_.*cos[c_.+d_.*x_]^2)*(b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*(b*Cos[c+d*x])^(n+1)/(b*d*(n+1)) + 
  (C*(n+1)+A*(n+2))/(b^2*(n+1))*Int[(b*Cos[c+d*x])^(n+2),x] /;
FreeQ[{b,c,d,A,C},x] && NonzeroQ[C*(n+1)+A*(n+2)] && RationalQ[n] && n<-1


Int[(A_+C_.*sin[c_.+d_.*x_]^2)*(b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*Cos[c+d*x]*(b*Sin[c+d*x])^(n+1)/(b*d*(n+2)) + 
  (C*(n+1)+A*(n+2))/(n+2)*Int[(b*Sin[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,C,n},x] && NonzeroQ[C*(n+1)+A*(n+2)] && Not[RationalQ[n] && n<-1]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)*(b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*Sin[c+d*x]*(b*Cos[c+d*x])^(n+1)/(b*d*(n+2)) + 
  (C*(n+1)+A*(n+2))/(n+2)*Int[(b*Cos[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,C,n},x] && NonzeroQ[C*(n+1)+A*(n+2)] && Not[RationalQ[n] && n<-1]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(b*Sin[c+d*x])^(n+1),x] + 
  Int[(A+C*Sin[c+d*x]^2)*(b*Sin[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,B,C,n},x]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(b*Cos[c+d*x])^(n+1),x] + 
  Int[(A+C*Cos[c+d*x]^2)*(b*Cos[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,B,C,n},x]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/b^2*Int[Simp[b*B-a*C+b*C*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/b^2*Int[Simp[b*B-a*C+b*C*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  C/b^2*Int[Simp[-a+b*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[A*b^2+a^2*C]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  C/b^2*Int[Simp[-a+b*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[A*b^2+a^2*C]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B+b*C)*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[a*A*(n+1)+n*(b*B-a*C)+b*C*(2*n+1)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B+b*C)*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(a*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[a*A*(n+1)+n*(b*B-a*C)+b*C*(2*n+1)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(A+C)*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[a*A*(n+1)-a*C*n+b*C*(2*n+1)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(A+C)*Sin[c+d*x]*(a+b*Cos[c+d*x])^n/(a*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[a*A*(n+1)-a*C*n+b*C*(2*n+1)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[n] && n<-1 && ZeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Simp[b*(a*A-b*B+a*C)*(n+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(n+1))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Simp[b*(a*A-b*B+a*C)*(n+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(n+1))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Simp[a*b*(A+C)*(n+1)-(A*b^2+a^2*C+b^2*(A+C)*(n+1))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Simp[a*b*(A+C)*(n+1)-(A*b^2+a^2*C+b^2*(A+C)*(n+1))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[n] && n<-1 && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Simp[A*b*(n+2)+b*C*(n+1)+(b*B*(n+2)-a*C)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[A*b^2-a*b*B+a^2*C]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Simp[A*b*(n+2)+b*C*(n+1)+(b*B*(n+2)-a*C)*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[A*b^2-a*b*B+a^2*C]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Simp[A*b*(n+2)+b*C*(n+1)-a*C*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[A*b^2+a^2*C]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*Sin[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Simp[A*b*(n+2)+b*C*(n+1)-a*C*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[A*b^2+a^2*C]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2)*(b*Sin[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,C,n},x] && IntegerQ[m]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2)*(b*Cos[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,C,n},x] && IntegerQ[m]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+C*Sin[c+d*x]^2)*(b*Sin[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,C,n},x] && IntegerQ[m]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+C*Cos[c+d*x]^2)*(b*Cos[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,C,n},x] && IntegerQ[m]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(b_*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Sin[c+d*x]]/Sqrt[Sin[c+d*x]]*Int[Sin[c+d*x]^(m+n)*(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(b_*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Cos[c+d*x]]/Sqrt[Cos[c+d*x]]*Int[Cos[c+d*x]^(m+n)*(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sin[c_.+d_.*x_]^m_*(A_+C_.*sin[c_.+d_.*x_]^2)*(b_*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Sin[c+d*x]]/Sqrt[Sin[c+d*x]]*Int[Sin[c+d*x]^(m+n)*(A+C*Sin[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[cos[c_.+d_.*x_]^m_*(A_+C_.*cos[c_.+d_.*x_]^2)*(b_*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Cos[c+d*x]]/Sqrt[Cos[c+d*x]]*Int[Cos[c+d*x]^(m+n)*(A+C*Cos[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(b_*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Sin[c+d*x]]/Sqrt[b*Sin[c+d*x]]*Int[Sin[c+d*x]^(m+n)*(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(b_*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Cos[c+d*x]]/Sqrt[b*Cos[c+d*x]]*Int[Cos[c+d*x]^(m+n)*(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sin[c_.+d_.*x_]^m_*(A_+C_.*sin[c_.+d_.*x_]^2)*(b_*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Sin[c+d*x]]/Sqrt[b*Sin[c+d*x]]*Int[Sin[c+d*x]^(m+n)*(A+C*Sin[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[cos[c_.+d_.*x_]^m_*(A_+C_.*cos[c_.+d_.*x_]^2)*(b_*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Cos[c+d*x]]/Sqrt[b*Cos[c+d*x]]*Int[Cos[c+d*x]^(m+n)*(A+C*Cos[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Sin[c+d*x])^n/Sin[c+d*x]^n*Int[Sin[c+d*x]^(m+n)*(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cos[c+d*x])^n/Cos[c+d*x]^n*Int[Cos[c+d*x]^(m+n)*(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Sin[c+d*x])^n/Sin[c+d*x]^n*Int[Sin[c+d*x]^(m+n)*(A+C*Sin[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C,m,n},x]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cos[c+d*x])^n/Cos[c+d*x]^n*Int[Cos[c+d*x]^(m+n)*(A+C*Cos[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C,m,n},x]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Int[Sin[c+d*x]^m*Simp[a*A+(b*B+a*C)*Sin[c+d*x]^2,x],x] + 
  Int[Sin[c+d*x]^(m+1)*Simp[A*b+a*B+b*C*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Int[Cos[c+d*x]^m*Simp[a*A+(b*B+a*C)*Cos[c+d*x]^2,x],x] + 
  Int[Cos[c+d*x]^(m+1)*Simp[A*b+a*B+b*C*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  a*Int[Sin[c+d*x]^m*(A+C*Sin[c+d*x]^2),x] + 
  b*Int[Sin[c+d*x]^(m+1)*(A+C*Sin[c+d*x]^2),x] /;
FreeQ[{a,b,c,d,A,C,m},x]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  a*Int[Cos[c+d*x]^m*(A+C*Cos[c+d*x]^2),x] + 
  b*Int[Cos[c+d*x]^(m+1)*(A+C*Cos[c+d*x]^2),x] /;
FreeQ[{a,b,c,d,A,C,m},x]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(a*b)*Int[Sin[c+d*x]^m*Simp[A*b+a*C*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && ZeroQ[A*b-a*B+b*C]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(a*b)*Int[Cos[c+d*x]^m*Simp[A*b+a*C*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && ZeroQ[A*b-a*B+b*C]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(a*b)*Int[Sin[c+d*x]^m*Simp[A*b+a*C*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && ZeroQ[A+C]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(a*b)*Int[Cos[c+d*x]^m*Simp[A*b+a*C*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && ZeroQ[A+C]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B+b*C)*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*
    Int[Sin[c+d*x]^m*
      Simp[a*A*(2*n+1)+(a*A-b*B+a*C)*(m+1)-(b*C*(m-n+1)+(A*b-a*B)*(m+n+2))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && NonzeroQ[A*b-a*B+b*C]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B+b*C)*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*
    Int[Cos[c+d*x]^m*
      Simp[a*A*(2*n+1)+(a*A-b*B+a*C)*(m+1)-(b*C*(m-n+1)+(A*b-a*B)*(m+n+2))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && NonzeroQ[A*b-a*B+b*C]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A+C)*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*
    Int[Sin[c+d*x]^m*Simp[a*A*(2*n+1)+a*(A+C)*(m+1)+(b*C*n-A*b*(n+1)-b*(A+C)*(m+1))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && NonzeroQ[A+C]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A+C)*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*
    Int[Cos[c+d*x]^m*Simp[a*A*(2*n+1)+a*(A+C)*(m+1)+(b*C*n-A*b*(n+1)-b*(A+C)*(m+1))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && NonzeroQ[A+C]


Int[sin[c_.+d_.*x_]^m_*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(m+1)) + 
  1/(a*(m+1))*Int[Sin[c+d*x]^(m+1)*Simp[a*B*(m+1)-A*b*n+a*(C*(m+1)+A*(m+n+2))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(m+1)) + 
  1/(a*(m+1))*Int[Cos[c+d*x]^(m+1)*Simp[a*B*(m+1)-A*b*n+a*(C*(m+1)+A*(m+n+2))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(m+1)) + 
  1/(a*(m+1))*Int[Sin[c+d*x]^(m+1)*Simp[-A*b*n+a*(C*(m+1)+A*(m+n+2))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(m+1)) + 
  1/(a*(m+1))*Int[Cos[c+d*x]^(m+1)*Simp[-A*b*n+a*(C*(m+1)+A*(m+n+2))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(m+n+2)) + 
  1/(a*(m+n+2))*Int[Sin[c+d*x]^m*Simp[a*C*(m+1)+a*A*(m+n+2)+(b*C*n+a*B*(m+n+2))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && ZeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(m+n+2)) + 
  1/(a*(m+n+2))*Int[Cos[c+d*x]^m*Simp[a*C*(m+1)+a*A*(m+n+2)+(b*C*n+a*B*(m+n+2))*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && ZeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(m+n+2)) + 
  1/(a*(m+n+2))*Int[Sin[c+d*x]^m*Simp[a*C*(m+1)+a*A*(m+n+2)+b*C*n*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(m+n+2)) + 
  1/(a*(m+n+2))*Int[Cos[c+d*x]^m*Simp[a*C*(m+1)+a*A*(m+n+2)+b*C*n*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[a^2-b^2]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  A*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  C*Int[Sin[c+d*x]^(3/2)/Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  A*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  C*Int[Cos[c+d*x]^(3/2)/Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  -C*Cos[c+d*x]*Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]/(b*d*(1+Sin[c+d*x])) + 
  C/b*Int[Sqrt[a+b*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(1+Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B] && ZeroQ[2*A*b-a*C]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  C*Sin[c+d*x]*Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]/(b*d*(1+Cos[c+d*x])) + 
  C/b*Int[Sqrt[a+b*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*(1+Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B] && ZeroQ[2*A*b-a*C]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(Sqrt[sin[c_.+d_.*x_]]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  1/(2*b)*Int[(2*A*b-a*C+(2*b*B-a*C)*Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  C/(2*b)*Int[Simp[a+a*Sin[c+d*x]+2*b*Sin[c+d*x]^2,x]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && Not[ZeroQ[A-B] && ZeroQ[2*A*b-a*C]]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(Sqrt[cos[c_.+d_.*x_]]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  1/(2*b)*Int[(2*A*b-a*C+(2*b*B-a*C)*Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  C/(2*b)*Int[Simp[a+a*Cos[c+d*x]+2*b*Cos[c+d*x]^2,x]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && Not[ZeroQ[A-B] && ZeroQ[2*A*b-a*C]]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*C*Cos[c+d*x]*Sin[c+d*x]^m*Sqrt[a+b*Sin[c+d*x]]/(b*d*(2*m+3)) + 
  1/(b*(2*m+3))*
    Int[Sin[c+d*x]^(m-1)*
      Simp[2*a*C*m+b*(2*A+(A+C)*(2*m+1))*Sin[c+d*x]+(b*B+2*(b*B-a*C)*(m+1))*Sin[c+d*x]^2,x]/
      Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*C*Sin[c+d*x]*Cos[c+d*x]^m*Sqrt[a+b*Cos[c+d*x]]/(b*d*(2*m+3)) + 
  1/(b*(2*m+3))*
    Int[Cos[c+d*x]^(m-1)*
      Simp[2*a*C*m+b*(2*A+(A+C)*(2*m+1))*Cos[c+d*x]+(b*B+2*(b*B-a*C)*(m+1))*Cos[c+d*x]^2,x]/
      Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*C*Cos[c+d*x]*Sin[c+d*x]^m*Sqrt[a+b*Sin[c+d*x]]/(b*d*(2*m+3)) + 
  1/(b*(2*m+3))*
    Int[Sin[c+d*x]^(m-1)*
      Simp[2*a*C*m+b*(2*A+(A+C)*(2*m+1))*Sin[c+d*x]-2*a*C*(m+1)*Sin[c+d*x]^2,x]/
      Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*C*Sin[c+d*x]*Cos[c+d*x]^m*Sqrt[a+b*Cos[c+d*x]]/(b*d*(2*m+3)) + 
  1/(b*(2*m+3))*
    Int[Cos[c+d*x]^(m-1)*
      Simp[2*a*C*m+b*(2*A+(A+C)*(2*m+1))*Cos[c+d*x]-2*a*C*(m+1)*Cos[c+d*x]^2,x]/
      Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(sin[c_.+d_.*x_]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  C/b*Int[Sqrt[a+b*Sin[c+d*x]],x] +
  1/b*Int[Simp[A*b+(b*B-a*C)*Sin[c+d*x],x]/(Sin[c+d*x]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(cos[c_.+d_.*x_]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  C/b*Int[Sqrt[a+b*Cos[c+d*x]],x] +
  1/b*Int[Simp[A*b+(b*B-a*C)*Cos[c+d*x],x]/(Cos[c+d*x]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)/(sin[c_.+d_.*x_]*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  C/b*Int[Sqrt[a+b*Sin[c+d*x]],x] + 
  1/b*Int[Simp[A*b-a*C*Sin[c+d*x],x]/(Sin[c+d*x]*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)/(cos[c_.+d_.*x_]*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  C/b*Int[Sqrt[a+b*Cos[c+d*x]],x] + 
  1/b*Int[Simp[A*b-a*C*Cos[c+d*x],x]/(Cos[c+d*x]*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  C*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[Simp[A+(B-C)*Sin[c+d*x],x]/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(cos[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  C*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  Int[Simp[A+(B-C)*Cos[c+d*x],x]/(Cos[c+d*x]^(3/2)*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)/(sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  C*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[Simp[A-C*Sin[c+d*x],x]/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)/(cos[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  C*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  Int[Simp[A-C*Cos[c+d*x],x]/(Cos[c+d*x]^(3/2)*Sqrt[a+b*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*
    Int[Sin[c+d*x]^(m+1)*
      Simp[2*(a*B-A*b)*(m+1)-A*b+2*a*(A+(A+C)*(m+1))*Sin[c+d*x]+A*b*(2*m+5)*Sin[c+d*x]^2,x]/
      Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*
    Int[Cos[c+d*x]^(m+1)*
      Simp[2*(a*B-A*b)*(m+1)-A*b+2*a*(A+(A+C)*(m+1))*Cos[c+d*x]+A*b*(2*m+5)*Cos[c+d*x]^2,x]/
      Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*Sqrt[a+b*Sin[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*
    Int[Sin[c+d*x]^(m+1)*
      Simp[-2*A*b*(m+1)-A*b+2*a*(A+(A+C)*(m+1))*Sin[c+d*x]+A*b*(2*m+5)*Sin[c+d*x]^2,x]/
      Sqrt[a+b*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*Sqrt[a+b*Cos[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*
    Int[Cos[c+d*x]^(m+1)*
      Simp[-2*A*b*(m+1)-A*b+2*a*(A+(A+C)*(m+1))*Cos[c+d*x]+A*b*(2*m+5)*Cos[c+d*x]^2,x]/
      Sqrt[a+b*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(m+1)) + 
  1/(m+1)*
    Int[Sin[c+d*x]^(m+1)*
      Simp[a*B*(m+1)-A*b*n+(a*A+(a*A+b*B+a*C)*(m+1))*Sin[c+d*x]+b*(C*(m+1)+A*(m+n+2))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>0 && m<-1


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(m+1)) + 
  1/(m+1)*
    Int[Cos[c+d*x]^(m+1)*
      Simp[a*B*(m+1)-A*b*n+(a*A+(a*A+b*B+a*C)*(m+1))*Cos[c+d*x]+b*(C*(m+1)+A*(m+n+2))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>0 && m<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(m+1)) + 
  1/(m+1)*
    Int[Sin[c+d*x]^(m+1)*
      Simp[-A*b*n+a*(A+(A+C)*(m+1))*Sin[c+d*x]+b*(C*(m+1)+A*(m+n+2))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>0 && m<-1


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(m+1)) + 
  1/(m+1)*
    Int[Cos[c+d*x]^(m+1)*
      Simp[-A*b*n+a*(A+(A+C)*(m+1))*Cos[c+d*x]+b*(C*(m+1)+A*(m+n+2))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>0 && m<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(m+n+2)) + 
  1/(m+n+2)*
    Int[Sin[c+d*x]^m*
      Simp[a*(C*(m+1)+A*(m+n+2))+(A*b+a*B+(A*b+a*B+b*C)*(m+n+1))*Sin[c+d*x]+(a*C*n+b*B*(m+n+2))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(m+n+2)) + 
  1/(m+n+2)*
    Int[Cos[c+d*x]^m*
      Simp[a*(C*(m+1)+A*(m+n+2))+(A*b+a*B+(A*b+a*B+b*C)*(m+n+1))*Cos[c+d*x]+(a*C*n+b*B*(m+n+2))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(d*(m+n+2)) + 
  1/(m+n+2)*
    Int[Sin[c+d*x]^m*
      Simp[a*(C*(m+1)+A*(m+n+2))+b*(A+(A+C)*(m+n+1))*Sin[c+d*x]+a*C*n*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(d*(m+n+2)) + 
  1/(m+n+2)*
    Int[Cos[c+d*x]^m*
      Simp[a*(C*(m+1)+A*(m+n+2))+b*(A+(A+C)*(m+n+1))*Cos[c+d*x]+a*C*n*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  (b*B-a*C)/b^2*Int[Sin[c+d*x]^m,x] + C/b*Int[Sin[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  (b*B-a*C)/b^2*Int[Cos[c+d*x]^m,x] + C/b*Int[Cos[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -a*C/b^2*Int[Sin[c+d*x]^m,x] + C/b*Int[Sin[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[A*b^2+a^2*C]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -a*C/b^2*Int[Cos[c+d*x]^m,x] + C/b*Int[Cos[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[A*b^2+a^2*C]


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  C/b*Int[Sqrt[Sin[c+d*x]],x] + 
  1/b*Int[Simp[A*b+(b*B-a*C)*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])),x_Symbol] :=
  C/b*Int[Sqrt[Cos[c+d*x]],x] + 
  1/b*Int[Simp[A*b+(b*B-a*C)*Cos[c+d*x],x]/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)/(Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  C/b*Int[Sqrt[Sin[c+d*x]],x] + 
  1/b*Int[Simp[A*b-a*C*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)/(Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])),x_Symbol] :=
  C/b*Int[Sqrt[Cos[c+d*x]],x] + 
  1/b*Int[Simp[A*b-a*C*Cos[c+d*x],x]/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -C*Cos[c+d*x]*Sin[c+d*x]^m/(b*d*(m+1)) + 
  1/(b*(m+1))*Int[Sin[c+d*x]^(m-1)*Simp[a*C*m+b*(A+m*(A+C))*Sin[c+d*x]+(b*B-a*C)*(m+1)*Sin[c+d*x]^2,x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  C*Sin[c+d*x]*Cos[c+d*x]^m/(b*d*(m+1)) + 
  1/(b*(m+1))*Int[Cos[c+d*x]^(m-1)*Simp[a*C*m+b*(A+m*(A+C))*Cos[c+d*x]+(b*B-a*C)*(m+1)*Cos[c+d*x]^2,x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -C*Cos[c+d*x]*Sin[c+d*x]^m/(b*d*(m+1)) + 
  1/(b*(m+1))*Int[Sin[c+d*x]^(m-1)*Simp[a*C*m+b*(A+m*(A+C))*Sin[c+d*x]-a*C*(m+1)*Sin[c+d*x]^2,x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  C*Sin[c+d*x]*Cos[c+d*x]^m/(b*d*(m+1)) + 
  1/(b*(m+1))*Int[Cos[c+d*x]^(m-1)*Simp[a*C*m+b*(A+m*(A+C))*Cos[c+d*x]-a*C*(m+1)*Cos[c+d*x]^2,x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Sin[c+d*x],x] - 
  1/a*Int[Simp[A*b-a*B-a*C*Sin[c+d*x],x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Cos[c+d*x],x] - 
  1/a*Int[Simp[A*b-a*B-a*C*Cos[c+d*x],x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)/(sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Sin[c+d*x],x] - 
  1/a*Int[Simp[A*b-a*C*Sin[c+d*x],x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)/(cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Cos[c+d*x],x] - 
  1/a*Int[Simp[A*b-a*C*Cos[c+d*x],x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(a*d*(m+1)) + 
  1/(a*(m+1))*
    Int[Sin[c+d*x]^(m+1)*Simp[(a*B-A*b)*(m+1)+a*(A+(A+C)*(m+1))*Sin[c+d*x]+A*b*(m+2)*Sin[c+d*x]^2,x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(a*d*(m+1)) + 
  1/(a*(m+1))*
    Int[Cos[c+d*x]^(m+1)*Simp[(a*B-A*b)*(m+1)+a*(A+(A+C)*(m+1))*Cos[c+d*x]+A*b*(m+2)*Cos[c+d*x]^2,x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  A*Cos[c+d*x]*Sin[c+d*x]^(m+1)/(a*d*(m+1)) + 
  1/(a*(m+1))*
    Int[Sin[c+d*x]^(m+1)*Simp[-A*b*(m+1)+a*(A+(A+C)*(m+1))*Sin[c+d*x]+A*b*(m+2)*Sin[c+d*x]^2,x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -A*Sin[c+d*x]*Cos[c+d*x]^(m+1)/(a*d*(m+1)) + 
  1/(a*(m+1))*
    Int[Cos[c+d*x]^(m+1)*Simp[-A*b*(m+1)+a*(A+(A+C)*(m+1))*Cos[c+d*x]+A*b*(m+2)*Cos[c+d*x]^2,x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[Sin[c+d*x]^m*Simp[b*B-a*C+b*C*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[Cos[c+d*x]^m*Simp[b*B-a*C+b*C*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  C/b^2*Int[Sin[c+d*x]^m*Simp[-a+b*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && ZeroQ[A*b^2+a^2*C]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  C/b^2*Int[Cos[c+d*x]^m*Simp[-a+b*Cos[c+d*x],x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && ZeroQ[A*b^2+a^2*C]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cos[c+d*x]*Sin[c+d*x]^m*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sin[c+d*x]^(m-1)*
      Simp[m*(A*b^2-a*b*B+a^2*C)+b*(a*A-b*B+a*C)*(n+1)*Sin[c+d*x]-
        ((A*b^2-a*b*B+b^2*C)*(n+1)+(A*b^2-a*b*B+a^2*C)*(m+1))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>0


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Sin[c+d*x]*Cos[c+d*x]^m*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Cos[c+d*x]^(m-1)*
      Simp[m*(A*b^2-a*b*B+a^2*C)+b*(a*A-b*B+a*C)*(n+1)*Cos[c+d*x]-
        ((A*b^2-a*b*B+b^2*C)*(n+1)+(A*b^2-a*b*B+a^2*C)*(m+1))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>0


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Cos[c+d*x]*Sin[c+d*x]^m*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sin[c+d*x]^(m-1)*
      Simp[m*(A*b^2+a^2*C)+b*(a*A+a*C)*(n+1)*Sin[c+d*x]-((A*b^2+b^2*C)*(n+1)+(A*b^2+a^2*C)*(m+1))*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>0


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Sin[c+d*x]*Cos[c+d*x]^m*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Cos[c+d*x]^(m-1)*
      Simp[m*(A*b^2+a^2*C)+b*(a*A+a*C)*(n+1)*Cos[c+d*x]-((A*b^2+b^2*C)*(n+1)+(A*b^2+a^2*C)*(m+1))*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>0


Int[(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)/(Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  C/b*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  1/b*Int[Simp[A*b-a*C+(b*B-C*(a+b))*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)/(Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  C/b*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  1/b*Int[Simp[A*b-a*C+(b*B-C*(a+b))*Cos[c+d*x],x]/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sin[c_.+d_.*x_]^2)/(Sqrt[sin[c_.+d_.*x_]]*(a_+b_.*sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  C/b*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  1/b*Int[Simp[A*b-a*C-C*(a+b)*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*cos[c_.+d_.*x_]^2)/(Sqrt[cos[c_.+d_.*x_]]*(a_+b_.*cos[c_.+d_.*x_])^(3/2)),x_Symbol] :=
  C/b*Int[(1+Cos[c+d*x])/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] + 
  1/b*Int[Simp[A*b-a*C-C*(a+b)*Cos[c+d*x],x]/(Sqrt[Cos[c+d*x]]*(a+b*Cos[c+d*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Sin[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-(A*b^2-a*b*B+a^2*C)*(m+1)-a*(A*b-a*B+b*C)*(n+1)*Sin[c+d*x]+
        (A*b^2-a*b*B+a^2*C)*(m+n+3)*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Cos[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-(A*b^2-a*b*B+a^2*C)*(m+1)-a*(A*b-a*B+b*C)*(n+1)*Cos[c+d*x]+
        (A*b^2-a*b*B+a^2*C)*(m+n+3)*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Cos[c+d*x]*Sin[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Sin[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-(A*b^2+a^2*C)*(m+1)-a*b*(A+C)*(n+1)*Sin[c+d*x]+(A*b^2+a^2*C)*(m+n+3)*Sin[c+d*x]^2,x]*
      (a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Sin[c+d*x]*Cos[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Cos[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-(A*b^2+a^2*C)*(m+1)-a*b*(A+C)*(n+1)*Cos[c+d*x]+(A*b^2+a^2*C)*(m+n+3)*Cos[c+d*x]^2,x]*
      (a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


(* Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Sin[c+d*x]^m*(a+b*Sin[c+d*x])^n,x] + 
  Int[Sin[c+d*x]^(m+1)*(B+C*Sin[c+d*x])*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Cos[c+d*x]^m*(a+b*Cos[c+d*x])^n,x] + 
  Int[Cos[c+d*x]^(m+1)*(B+C*Cos[c+d*x])*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Sin[c+d*x]^m*(a+b*Sin[c+d*x])^n,x] + 
  C*Int[Sin[c+d*x]^(m+2)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Cos[c+d*x]^m*(a+b*Cos[c+d*x])^n,x] + 
  C*Int[Cos[c+d*x]^(m+2)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && NonzeroQ[a^2-b^2] *)


Int[sin[c_.+d_.*x_]^m_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Sin[c+d*x]^m*(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Cos[c+d*x]^m*(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Sin[c+d*x]^m*(A+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Cos[c+d*x]^m*(A+C*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && NonzeroQ[a^2-b^2]


Int[(e_.*csc[c_.+d_.*x_])^m_*(A_.+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Csc[c+d*x])^m*Sin[c+d*x]^m*Int[(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2)/Sin[c+d*x]^m,x] /;
FreeQ[{c,d,e,A,B,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*sec[c_.+d_.*x_])^m_*(A_.+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Sec[c+d*x])^m*Cos[c+d*x]^m*Int[(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2)/Cos[c+d*x]^m,x] /;
FreeQ[{c,d,e,A,B,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*csc[c_.+d_.*x_])^m_*(A_.+C_.*sin[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Csc[c+d*x])^m*Sin[c+d*x]^m*Int[(A+C*Sin[c+d*x]^2)/Sin[c+d*x]^m,x] /;
FreeQ[{c,d,e,A,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*sec[c_.+d_.*x_])^m_*(A_.+C_.*cos[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Sec[c+d*x])^m*Cos[c+d*x]^m*Int[(A+C*Cos[c+d*x]^2)/Cos[c+d*x]^m,x] /;
FreeQ[{c,d,e,A,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*csc[c_.+d_.*x_])^m_.*(f_.*sin[c_.+d_.*x_])^p_.*(A_.+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Csc[c+d*x])^m*(f*Sin[c+d*x])^p/Sin[c+d*x]^(p-m)*Int[Sin[c+d*x]^(p-m)*(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,B,C,m,p},x]


Int[(e_.*sec[c_.+d_.*x_])^m_.*(f_.*cos[c_.+d_.*x_])^p_.*(A_.+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Sec[c+d*x])^m*(f*Cos[c+d*x])^p/Cos[c+d*x]^(p-m)*Int[Cos[c+d*x]^(p-m)*(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,B,C,m,p},x]


Int[(e_.*csc[c_.+d_.*x_])^m_.*(f_.*sin[c_.+d_.*x_])^p_.*(A_.+C_.*sin[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Csc[c+d*x])^m*(f*Sin[c+d*x])^p/Sin[c+d*x]^(p-m)*Int[Sin[c+d*x]^(p-m)*(A+C*Sin[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,C,m,p},x]


Int[(e_.*sec[c_.+d_.*x_])^m_.*(f_.*cos[c_.+d_.*x_])^p_.*(A_.+C_.*cos[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Sec[c+d*x])^m*(f*Cos[c+d*x])^p/Cos[c+d*x]^(p-m)*Int[Cos[c+d*x]^(p-m)*(A+C*Cos[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,C,m,p},x]


Int[(e_*sin[c_.+d_.*x_])^m_*(A_.+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m/Sin[c+d*x]^m*Int[Sin[c+d*x]^m*(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*cos[c_.+d_.*x_])^m_*(A_.+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m/Cos[c+d*x]^m*Int[Cos[c+d*x]^m*(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*sin[c_.+d_.*x_])^m_*(A_.+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m/Sin[c+d*x]^m*Int[Sin[c+d*x]^m*(A+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*cos[c_.+d_.*x_])^m_*(A_.+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m/Cos[c+d*x]^m*Int[Cos[c+d*x]^m*(A+C*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*csc[c_.+d_.*x_])^m_*(A_.+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m*Sin[c+d*x]^m*Int[(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*sec[c_.+d_.*x_])^m_*(A_.+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m*Cos[c+d*x]^m*Int[(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n/Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*csc[c_.+d_.*x_])^m_*(A_.+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m*Sin[c+d*x]^m*Int[(A+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*sec[c_.+d_.*x_])^m_*(A_.+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m*Cos[c+d*x]^m*Int[(A+C*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n/Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*csc[c_.+d_.*x_])^m_.*(f_.*sin[c_.+d_.*x_])^p_.*(A_.+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m*(f*Sin[c+d*x])^p/Sin[c+d*x]^(p-m)*Int[Sin[c+d*x]^(p-m)*(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x]


Int[(e_.*sec[c_.+d_.*x_])^m_.*(f_.*cos[c_.+d_.*x_])^p_.*(A_.+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m*(f*Cos[c+d*x])^p/Cos[c+d*x]^(p-m)*Int[Cos[c+d*x]^(p-m)*(A+B*Cos[c+d*x]+C*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x]


Int[(e_.*csc[c_.+d_.*x_])^m_.*(f_.*sin[c_.+d_.*x_])^p_.*(A_.+C_.*sin[c_.+d_.*x_]^2)*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m*(f*Sin[c+d*x])^p/Sin[c+d*x]^(p-m)*Int[Sin[c+d*x]^(p-m)*(A+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n,p},x]


Int[(e_.*sec[c_.+d_.*x_])^m_.*(f_.*cos[c_.+d_.*x_])^p_.*(A_.+C_.*cos[c_.+d_.*x_]^2)*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m*(f*Cos[c+d*x])^p/Cos[c+d*x]^(p-m)*Int[Cos[c+d*x]^(p-m)*(A+C*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n,p},x]


Int[u_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Sin[c+d*x]+A*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x]


Int[u_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Cos[c+d*x]+A*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n/Cos[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x]


Int[u_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,C,n},x]


Int[u_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^n/Cos[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,C,n},x]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/(Sqrt[sin[c_.+d_.*x_]]*(A_+B_.*sin[c_.+d_.*x_])),x_Symbol] :=
  -Sqrt[a+b]/(A*d)*EllipticE[ArcSin[Cos[c+d*x]/(1+Sin[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[B-A] && PositiveQ[b] && PositiveQ[b^2-a^2]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/(Sqrt[cos[c_.+d_.*x_]]*(A_+B_.*cos[c_.+d_.*x_])),x_Symbol] :=
  Sqrt[a+b]/(A*d)*EllipticE[ArcSin[Sin[c+d*x]/(1+Cos[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[B-A] && PositiveQ[b] && PositiveQ[b^2-a^2]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/(Sqrt[sin[c_.+d_.*x_]]*(A_+B_.*sin[c_.+d_.*x_])),x_Symbol] :=
  -(a+b)*Sqrt[1+Sin[c+d*x]]*Sqrt[(a+b*Sin[c+d*x])/((a+b)*(1+Sin[c+d*x]))]/(A*d*Sqrt[a+b*Sin[c+d*x]])*
    EllipticE[ArcSin[Cos[c+d*x]/(1+Sin[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*cos[c_.+d_.*x_]]/(Sqrt[cos[c_.+d_.*x_]]*(A_+B_.*cos[c_.+d_.*x_])),x_Symbol] :=
  (a+b)*Sqrt[1+Cos[c+d*x]]*Sqrt[(a+b*Cos[c+d*x])/((a+b)*(1+Cos[c+d*x]))]/(A*d*Sqrt[a+b*Cos[c+d*x]])*
    EllipticE[ArcSin[Sin[c+d*x]/(1+Cos[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2]


(* Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]]/(Sqrt[sin[c_.+d_.*x_]]*(A_+B_.*sin[c_.+d_.*x_])),x_Symbol] :=
  -Sqrt[a+b*Sin[c+d*x]]/(A*d*Sqrt[1+Sin[c+d*x]]*Sqrt[(a+b*Sin[c+d*x])/((a+b)*(1+Sin[c+d*x]))])*
    EllipticE[ArcSin[Cos[c+d*x]/(1+Sin[c+d*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2] *)


Int[Sqrt[sin[c_.+d_.*x_]]/(Sqrt[a_.+b_.*sin[c_.+d_.*x_]]*(A_+B_.*sin[c_.+d_.*x_])),x_Symbol] :=
  a/(A*(a-b))*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] - 
  1/(a-b)*Int[Sqrt[a+b*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(A+B*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]


Int[Sqrt[cos[c_.+d_.*x_]]/(Sqrt[a_.+b_.*cos[c_.+d_.*x_]]*(A_+B_.*cos[c_.+d_.*x_])),x_Symbol] :=
  a/(A*(a-b))*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Cos[c+d*x]]),x] - 
  1/(a-b)*Int[Sqrt[a+b*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*(A+B*Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]


(* ::Subsection::Closed:: *)
(*7.1.4 cos(c+d x)^m (a+b sin(c+d x))^n*)


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Module[{e=FreeFactors[Sin[c+d*x],x]},
  e/d*Subst[Int[(1-e^2*x^2)^((m-1)/2)*(a+b*e*x)^n,x],x,Sin[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && OddQ[m]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Module[{e=FreeFactors[Cos[c+d*x],x]},
  -e/d*Subst[Int[(1-e^2*x^2)^((m-1)/2)*(a+b*e*x)^n,x],x,Cos[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && OddQ[m]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Cos[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(a*d*n) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  -b*Sin[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(a*d*n) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Cos[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-1)/(d*(n-1)) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+2*n-1] && NonzeroQ[n-1]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Sin[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-1)/(d*(n-1)) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+2*n-1] && NonzeroQ[n-1]


Int[(a_+b_.*sin[c_.+d_.*x_])/cos[c_.+d_.*x_],x_Symbol] :=
  -b*Log[RemoveContent[a-b*Sin[c+d*x],x]]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[(a_+b_.*cos[c_.+d_.*x_])/sin[c_.+d_.*x_],x_Symbol] :=
  b*Log[RemoveContent[a-b*Cos[c+d*x],x]]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -b*Cos[c+d*x]^(m+1)/(d*(m+1)) + a*Int[Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m+1]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  b*Sin[c+d*x]^(m+1)/(d*(m+1)) + a*Int[Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m+1]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(a*d*(m+1)) + 
  a*(m+n+1)/(m+1)*Int[Cos[c+d*x]^(m+2)*(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 0<n<1 && m<-1 && NonzeroQ[m+n+1]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(a*d*(m+1)) + 
  a*(m+n+1)/(m+1)*Int[Sin[c+d*x]^(m+2)*(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 0<n<1 && m<-1 && NonzeroQ[m+n+1]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -2*b*Cos[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-1)/(d*(m+1)) + 
  b^2*(m+2*n-1)/(m+1)*Int[Cos[c+d*x]^(m+2)*(a+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1 && NonzeroQ[m+2*n-1]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  2*b*Sin[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-1)/(d*(m+1)) + 
  b^2*(m+2*n-1)/(m+1)*Int[Sin[c+d*x]^(m+2)*(a+b*Cos[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1 && NonzeroQ[m+2*n-1]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  -b*Cos[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^(n-1)/(d*(m+n)) + 
  a*(m+2*n-1)/(m+n)*Int[Cos[c+d*x]^m*(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  b*Sin[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^(n-1)/(d*(m+n)) + 
  a*(m+2*n-1)/(m+n)*Int[Sin[c+d*x]^m*(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n]


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Cos[c+d*x]^(m-1)/(b*d*(m-1)) + 
  1/a*Int[Cos[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m-1]


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -Sin[c+d*x]^(m-1)/(b*d*(m-1)) + 
  1/a*Int[Sin[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m-1]


Int[cos[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*b*Cos[c+d*x]^(m+1)/(d*(2*m-1)*(a+b*Sin[c+d*x])^(3/2)) + 
  2*a*(m-2)/(2*m-1)*Int[Cos[c+d*x]^m/(a+b*Sin[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>2


Int[sin[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  2*b*Sin[c+d*x]^(m+1)/(d*(2*m-1)*(a+b*Cos[c+d*x])^(3/2)) + 
  2*a*(m-2)/(2*m-1)*Int[Sin[c+d*x]^m/(a+b*Cos[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>2


Int[1/(cos[c_.+d_.*x_]^2*Sqrt[a_+b_.*sin[c_.+d_.*x_]]),x_Symbol] :=
  Tan[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]]) + 
  b/2*Int[Sin[c+d*x]/(a+b*Sin[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/(sin[c_.+d_.*x_]^2*Sqrt[a_+b_.*cos[c_.+d_.*x_]]),x_Symbol] :=
  -Cot[c+d*x]/(d*Sqrt[a+b*Cos[c+d*x]]) + 
  b/2*Int[Cos[c+d*x]/(a+b*Cos[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -b*Cos[c+d*x]^(m+1)/(a*d*(m+1)*Sqrt[a+b*Sin[c+d*x]]) + 
  a*(2*m+1)/(2*(m+1))*Int[Cos[c+d*x]^(m+2)/(a+b*Sin[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-2


Int[sin[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cos[c_.+d_.*x_]],x_Symbol] :=
  b*Sin[c+d*x]^(m+1)/(a*d*(m+1)*Sqrt[a+b*Cos[c+d*x]]) + 
  a*(2*m+1)/(2*(m+1))*Int[Sin[c+d*x]^(m+2)/(a+b*Cos[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-2


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]^(m-1)*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) + 
  2/a*Int[Cos[c+d*x]^(m-2)*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m+2*n+1==0


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]^(m-1)*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)) + 
  2/a*Int[Sin[c+d*x]^(m-2)*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m+2*n+1==0


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  2*Cos[c+d*x]^(m-1)*(a+b*Sin[c+d*x])^(n+1)/(b*d*(m+2*n+1)) + 
  (m-1)/(b^2*(m+2*n+1))*Int[Cos[c+d*x]^(m-2)*(a+b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m+2*n+1!=0 && m>1


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -2*Sin[c+d*x]^(m-1)*(a+b*Cos[c+d*x])^(n+1)/(b*d*(m+2*n+1)) + 
  (m-1)/(b^2*(m+2*n+1))*Int[Sin[c+d*x]^(m-2)*(a+b*Cos[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m+2*n+1!=0 && m>1


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Cos[c+d*x]^(m+1)*(a+b*Sin[c+d*x])^n/(a*d*(m+2*n+1)) + 
  (m+n+1)/(a*(m+2*n+1))*Int[Cos[c+d*x]^m*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1 && NonzeroQ[m+2*n+1] && Not[RationalQ[m] && m>1]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  -b*Sin[c+d*x]^(m+1)*(a+b*Cos[c+d*x])^n/(a*d*(m+2*n+1)) + 
  (m+n+1)/(a*(m+2*n+1))*Int[Sin[c+d*x]^m*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1 && NonzeroQ[m+2*n+1] && Not[RationalQ[m] && m>1]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[Cos[c+d*x]^m,(a+b*Sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[Sin[c+d*x]^m,(a+b*Cos[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[n]


Int[cos[c_.+d_.*x_]^4*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a^2-b^2)*Cos[c+d*x]*Sin[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(a*b^2*d*(n+1)) - 
  Cos[c+d*x]*Sin[c+d*x]*(a+b*Sin[c+d*x])^(n+2)/(b^2*d*(n+4)) - 
  1/(a*b^2*(n+1)*(n+4))*Int[(a+b*Sin[c+d*x])^(n+1)*
    Simp[3*a^2-b^2*(n+2)*(n+4)+a*b*(n+1)*Sin[c+d*x]-(6*a^2-b^2*(n+3)*(n+4))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && -2<=n<-1


Int[sin[c_.+d_.*x_]^4*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a^2-b^2)*Sin[c+d*x]*Cos[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(a*b^2*d*(n+1)) + 
  Sin[c+d*x]*Cos[c+d*x]*(a+b*Cos[c+d*x])^(n+2)/(b^2*d*(n+4)) - 
  1/(a*b^2*(n+1)*(n+4))*Int[(a+b*Cos[c+d*x])^(n+1)*
    Simp[3*a^2-b^2*(n+2)*(n+4)+a*b*(n+1)*Cos[c+d*x]-(6*a^2-b^2*(n+3)*(n+4))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && -2<=n<-1


Int[cos[c_.+d_.*x_]^4*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a^2-b^2)*Cos[c+d*x]*Sin[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(a*b^2*d*(n+1)) - 
  (a^2*(n-1)+b^2*(n+2))*Cos[c+d*x]*Sin[c+d*x]*(a+b*Sin[c+d*x])^(n+2)/(a^2*b^2*d*(n+1)*(n+2)) - 
  1/(a^2*b^2*(n+1)*(n+2))*Int[(a+b*Sin[c+d*x])^(n+2)*
    Simp[3*a^2-b^2*(n+2)*(n+3)+a*b*(n+2)*Sin[c+d*x]-(6*a^2-b^2*(n+2)*(n+4))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-2


Int[sin[c_.+d_.*x_]^4*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a^2-b^2)*Sin[c+d*x]*Cos[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(a*b^2*d*(n+1)) + 
  (a^2*(n-1)+b^2*(n+2))*Sin[c+d*x]*Cos[c+d*x]*(a+b*Cos[c+d*x])^(n+2)/(a^2*b^2*d*(n+1)*(n+2)) - 
  1/(a^2*b^2*(n+1)*(n+2))*Int[(a+b*Cos[c+d*x])^(n+2)*
    Simp[3*a^2-b^2*(n+2)*(n+3)+a*b*(n+2)*Cos[c+d*x]-(6*a^2-b^2*(n+2)*(n+4))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-2


Int[cos[c_.+d_.*x_]^4*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  3*a*Cos[c+d*x]*Sin[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b^2*d*(n+3)*(n+4)) - 
  Cos[c+d*x]*Sin[c+d*x]^2*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+4)) - 
  1/(b^2*(n+3)*(n+4))*Int[(a+b*Sin[c+d*x])^n*
    Simp[3*a^2-b^2*(n+3)*(n+4)+a*b*n*Sin[c+d*x]-(6*a^2-b^2*(n+3)*(n+5))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[n] && n<-1]


Int[sin[c_.+d_.*x_]^4*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -3*a*Sin[c+d*x]*Cos[c+d*x]*(a+b*Cos[c+d*x])^(n+1)/(b^2*d*(n+3)*(n+4)) + 
  Sin[c+d*x]*Cos[c+d*x]^2*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+4)) - 
  1/(b^2*(n+3)*(n+4))*Int[(a+b*Cos[c+d*x])^n*
    Simp[3*a^2-b^2*(n+3)*(n+4)+a*b*n*Cos[c+d*x]-(6*a^2-b^2*(n+3)*(n+5))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[n] && n<-1]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Cos[c+d*x]^(m-1)*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) + 
  (m-1)/(b*(n+1))*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && NonzeroQ[n+1] && PositiveIntegerQ[m] && m<=4


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -Sin[c+d*x]^(m-1)*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)) + 
  (m-1)/(b*(n+1))*Int[Sin[c+d*x]^(m-2)*Cos[c+d*x]*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && NonzeroQ[n+1] && PositiveIntegerQ[m] && m<=4


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(1-sin[c+d*x]^2)^(m/2)*(a+b*sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && EvenQ[m] && m>2 && IntegerQ[n] && n<-1


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(1-cos[c+d*x]^2)^(m/2)*(a+b*cos[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && EvenQ[m] && m>2 && IntegerQ[n] && n<-1


Int[(a_+b_.*sin[c_.+d_.*x_])^n_./cos[c_.+d_.*x_]^2,x_Symbol] :=
  Tan[c+d*x]*(a+b*Sin[c+d*x])^n/d - 
  b*n*Int[Sin[c+d*x]*(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && NonzeroQ[n+1]


Int[(a_+b_.*cos[c_.+d_.*x_])^n_./sin[c_.+d_.*x_]^2,x_Symbol] :=
  -Cot[c+d*x]*(a+b*Cos[c+d*x])^n/d - 
  b*n*Int[Cos[c+d*x]*(a+b*Cos[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && NonzeroQ[n+1]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(1-Sin[c+d*x]^2)^(m/2)*(a+b*Sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && EvenQ[m] && m<-2 && IntegerQ[n] && n<-1


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(1-Cos[c+d*x]^2)^(m/2)*(a+b*Cos[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && EvenQ[m] && m<-2 && IntegerQ[n] && n<-1


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a^2-b^2)*Int[Cos[c+d*x]^m*(a+b*Sin[c+d*x])^(n-2),x] + 
  2*a*Int[Cos[c+d*x]^m*(a+b*Sin[c+d*x])^(n-1),x] - 
  b^2*Int[Cos[c+d*x]^(m+2)*(a+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m<-1 && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a^2-b^2)*Int[Cos[c+d*x]^m*(a+b*Sin[c+d*x])^(n-2),x] + 
  2*a*Int[Cos[c+d*x]^m*(a+b*Sin[c+d*x])^(n-1),x] - 
  b^2*Int[Cos[c+d*x]^(m+2)*(a+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m<-1 && NonzeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Cos[c+d*x]^(m-1)/(b*d*(m-1)) + 
  a/b^2*Int[Cos[c+d*x]^(m-2),x] - 
  (a^2-b^2)/b^2*Int[Cos[c+d*x]^(m-2)/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -Sin[c+d*x]^(m-1)/(b*d*(m-1)) + 
  a/b^2*Int[Sin[c+d*x]^(m-2),x] - 
  (a^2-b^2)/b^2*Int[Sin[c+d*x]^(m-2)/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  b*Cos[c+d*x]^(m+1)/(d*(m+1)*(a^2-b^2)) + 
  a/(a^2-b^2)*Int[Cos[c+d*x]^m,x] - 
  b^2/(a^2-b^2)*Int[Cos[c+d*x]^(m+2)/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  -b*Sin[c+d*x]^(m+1)/(d*(m+1)*(a^2-b^2)) + 
  a/(a^2-b^2)*Int[Sin[c+d*x]^m,x] - 
  b^2/(a^2-b^2)*Int[Sin[c+d*x]^(m+2)/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


(* ::Subsection::Closed:: *)
(*7.1.5 cos(c+d x)^m sin(c+d x)^n (a+b sin(c+d x))^p*)


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  a*Int[Cos[c+d*x]^m*Sin[c+d*x]^n,x] + b*Int[Cos[c+d*x]^m*Sin[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d,m,n},x] && (Not[OddQ[m]] || NonzeroQ[a^2-b^2] && m<0 || RationalQ[n] && (0<n<m-1 || -2*m<=n<-m-1))


Int[sin[c_.+d_.*x_]^m_.*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  a*Int[Sin[c+d*x]^m*Cos[c+d*x]^n,x] + b*Int[Sin[c+d*x]^m*Cos[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d,m,n},x] && (Not[OddQ[m]] || NonzeroQ[a^2-b^2] && m<0 || RationalQ[n] && (0<n<m-1 || -2*m<=n<-m-1))


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Module[{e=FreeFactors[Sin[c+d*x],x]},
  e/d*Subst[Int[(e*x)^n*(1-e^2*x^2)^((m-1)/2)*(a+b*e*x),x],x,Sin[c+d*x]/e]] /;
FreeQ[{a,b,c,d},x] && OddQ[m]


Int[sin[c_.+d_.*x_]^m_.*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Module[{e=FreeFactors[Cos[c+d*x],x]},
  -e/d*Subst[Int[(e*x)^n*(1-e^2*x^2)^((m-1)/2)*(a+b*e*x),x],x,Cos[c+d*x]/e]] /;
FreeQ[{a,b,c,d},x] && OddQ[m]


Int[cos[c_.+d_.*x_]*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Module[{e=FreeFactors[Sin[c+d*x],x]},
  e/d*Subst[Int[(e*x)^n*(a+b*e*x)^p,x],x,Sin[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n,p},x]


Int[sin[c_.+d_.*x_]*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Module[{e=FreeFactors[Cos[c+d*x],x]},
  -e/d*Subst[Int[(e*x)^n*(a+b*e*x)^p,x],x,Cos[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n,p},x]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_./(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]^n,x] - 
  1/b*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && (Not[PositiveIntegerQ[(m+1)/2]] || ZeroQ[n-1] || ZeroQ[m-3] || ZeroQ[m+n] || ZeroQ[m+n+1])


Int[sin[c_.+d_.*x_]^m_.*cos[c_.+d_.*x_]^n_./(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[Sin[c+d*x]^(m-2)*Cos[c+d*x]^n,x] - 
  1/b*Int[Sin[c+d*x]^(m-2)*Cos[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && (Not[PositiveIntegerQ[(m+1)/2]] || ZeroQ[n-1] || ZeroQ[m-3] || ZeroQ[m+n] || ZeroQ[m+n+1])


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Module[{e=FreeFactors[Sin[c+d*x],x]},
  e/d*Subst[Int[(e*x)^n*(1-e^2*x^2)^((m-1)/2)*(a+b*e*x)^p,x],x,Sin[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[a^2-b^2] && OddQ[m]


Int[sin[c_.+d_.*x_]^m_*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Module[{e=FreeFactors[Cos[c+d*x],x]},
  -e/d*Subst[Int[(e*x)^n*(1-e^2*x^2)^((m-1)/2)*(a+b*e*x)^p,x],x,Cos[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[a^2-b^2] && OddQ[m]


Int[cos[c_.+d_.*x_]^2*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  1/a^2*Int[Sin[c+d*x]^n*(a-b*Sin[c+d*x])*(a+b*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^2*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  1/a^2*Int[Cos[c+d*x]^n*(a-b*Cos[c+d*x])*(a+b*Cos[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[a^2-b^2]


Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[Sin[c+d*x]^(n+4)*(a+b*Sin[c+d*x])^p,x] + 
  Int[Sin[c+d*x]^n*(1-2*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && IntegerQ[p+1/2] && p>-1


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[Cos[c+d*x]^(n+4)*(a+b*Cos[c+d*x])^p,x] + 
  Int[Cos[c+d*x]^n*(1-2*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && IntegerQ[p+1/2] && p>-1


Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -2/(a*b)*Int[Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+2),x] + 
  1/a^2*Int[Sin[c+d*x]^n*(1+Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && (IntegerQ[p+1/2] && p<-1 || ZeroQ[p+2])


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -2/(a*b)*Int[Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+2),x] + 
  1/a^2*Int[Cos[c+d*x]^n*(1+Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && (IntegerQ[p+1/2] && p<-1 || ZeroQ[p+2])


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  a^(2*p)*Int[Cos[c+d*x]^(m+2*p)*Sin[c+d*x]^n/(a-b*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && Not[OddQ[m]] && IntegerQ[p] && (NegativeIntegerQ[m,p] || ZeroQ[m+2*p] || ZeroQ[m+2*p-2])


Int[sin[c_.+d_.*x_]^m_*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  a^(2*p)*Int[Sin[c+d*x]^(m+2*p)*Cos[c+d*x]^n/(a-b*Cos[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && Not[OddQ[m]] && IntegerQ[p] && (NegativeIntegerQ[m,p] || ZeroQ[m+2*p] || ZeroQ[m+2*p-2])


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  1/a^m*Int[ExpandTrig[Sin[c+d*x]^n*(a-b*Sin[c+d*x])^(m/2)*(a+b*Sin[c+d*x])^(p+m/2),x],x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && IntegersQ[m/2,p] && (p<-2 && m>0 || p>2 && m<0 && p+m/2>0 || m>2 && p>=2 && RationalQ[n] && -p-m<n<-1)


Int[sin[c_.+d_.*x_]^m_*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  1/a^m*Int[ExpandTrig[Cos[c+d*x]^n*(a-b*Cos[c+d*x])^(m/2)*(a+b*Cos[c+d*x])^(p+m/2),x],x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && IntegersQ[m/2,p] && (p<-2 && m>0 || p>2 && m<0 && p+m/2>0 || m>2 && p>=2 && RationalQ[n] && -p-m<n<-1)


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n,(a+b*sin[c+d*x])^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && Not[OddQ[m]] && PositiveIntegerQ[p]


Int[sin[c_.+d_.*x_]^m_.*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[ExpandTrig[sin[c+d*x]^m*cos[c+d*x]^n,(a+b*cos[c+d*x])^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2-b^2] && Not[OddQ[m]] && PositiveIntegerQ[p]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Module[{e=FreeFactors[Sin[c+d*x],x]},
  e/d*Subst[Int[(e*x)^n*(1-e^2*x^2)^((m-1)/2)*(a+b*e*x)^p,x],x,Sin[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n,p},x] && OddQ[m]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Module[{e=FreeFactors[Cos[c+d*x],x]},
  -e/d*Subst[Int[(e*x)^m*(1-e^2*x^2)^((n-1)/2)*(a+b*e*x)^p,x],x,Cos[c+d*x]/e]] /;
FreeQ[{a,b,c,d,m,p},x] && OddQ[n]


Int[cos[c_.+d_.*x_]^2*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[Sin[c+d*x]^n*(1-Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && NonzeroQ[a^2-b^2]


Int[sin[c_.+d_.*x_]^2*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[Cos[c+d*x]^n*(1-Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && NonzeroQ[a^2-b^2]


(* Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (a^2-b^2)*Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)/(a*b^2*d*(p+1)) - 
  (a^2*(n+1)-b^2*(n+p+2))*Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+2)/(a^2*b^2*d*(n+1)*(p+1)) + 
  1/(a^2*b*(n+1)*(p+1))*Int[Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(n+p+2)*(n+p+3)+a*b*(p+1)*Sin[c+d*x]-(a^2*(n+1)*(n+3)-b^2*(n+p+2)*(n+p+4))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p<-1 && n<-1 *)


(* Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -(a^2-b^2)*Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)/(a*b^2*d*(p+1)) + 
  (a^2*(n+1)-b^2*(n+p+2))*Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+2)/(a^2*b^2*d*(n+1)*(p+1)) + 
  1/(a^2*b*(n+1)*(p+1))*Int[Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(n+p+2)*(n+p+3)+a*b*(p+1)*Cos[c+d*x]-(a^2*(n+1)*(n+3)-b^2*(n+p+2)*(n+p+4))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p<-1 && n<-1 *)


Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)/(a*d*(n+1)) - 
  (a^2*(n+1)-b^2*(2+n+p))*Cos[c+d*x]*Sin[c+d*x]^(n+2)*(a+b*Sin[c+d*x])^(p+1)/(a^2*b*d*(n+1)*(p+1)) + 
  1/(a^2*b*(n+1)*(p+1))*Int[Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(n+p+2)*(n+p+3)+a*b*(p+1)*Sin[c+d*x]-(a^2*(n+1)*(n+3)-b^2*(n+p+2)*(n+p+4))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p<-1 && n<-1


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)/(a*d*(n+1)) + 
  (a^2*(n+1)-b^2*(2+n+p))*Sin[c+d*x]*Cos[c+d*x]^(n+2)*(a+b*Cos[c+d*x])^(p+1)/(a^2*b*d*(n+1)*(p+1)) + 
  1/(a^2*b*(n+1)*(p+1))*Int[Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(n+p+2)*(n+p+3)+a*b*(p+1)*Cos[c+d*x]-(a^2*(n+1)*(n+3)-b^2*(n+p+2)*(n+p+4))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n,p] && p<-1 && n<-1


Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (a^2-b^2)*Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)/(a*b^2*d*(p+1)) + 
  (a^2*(n-p+1)-b^2*(n+p+2))*Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+2)/(a^2*b^2*d*(p+1)*(p+2)) - 
  1/(a^2*b^2*(p+1)*(p+2))*Int[Sin[c+d*x]^n*(a+b*Sin[c+d*x])^(p+2)*
    Simp[a^2*(n+1)*(n+3)-b^2*(n+p+2)*(n+p+3)+a*b*(p+2)*Sin[c+d*x]-(a^2*(n+2)*(n+3)-b^2*(n+p+2)*(n+p+4))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1 && Not[RationalQ[n] && n<-1] && (p<-2 || ZeroQ[n+p+4])


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -(a^2-b^2)*Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)/(a*b^2*d*(p+1)) - 
  (a^2*(n-p+1)-b^2*(n+p+2))*Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+2)/(a^2*b^2*d*(p+1)*(p+2)) - 
  1/(a^2*b^2*(p+1)*(p+2))*Int[Cos[c+d*x]^n*(a+b*Cos[c+d*x])^(p+2)*
    Simp[a^2*(n+1)*(n+3)-b^2*(n+p+2)*(n+p+3)+a*b*(p+2)*Cos[c+d*x]-(a^2*(n+2)*(n+3)-b^2*(n+p+2)*(n+p+4))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1 && Not[RationalQ[n] && n<-1] && (p<-2 || ZeroQ[n+p+4])


Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (a^2-b^2)*Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)/(a*b^2*d*(p+1)) - 
  Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+2)/(b^2*d*(n+p+4)) - 
  1/(a*b^2*(p+1)*(n+p+4))*Int[Sin[c+d*x]^n*(a+b*Sin[c+d*x])^(p+1)*
    Simp[a^2*(n+1)*(n+3)-b^2*(n+p+2)*(n+p+4)+a*b*(p+1)*Sin[c+d*x]-(a^2*(n+2)*(n+3)-b^2*(n+p+3)*(n+p+4))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1 && Not[RationalQ[n] && n<-1] && NonzeroQ[n+p+4]


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -(a^2-b^2)*Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)/(a*b^2*d*(p+1)) + 
  Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+2)/(b^2*d*(n+p+4)) - 
  1/(a*b^2*(p+1)*(n+p+4))*Int[Cos[c+d*x]^n*(a+b*Cos[c+d*x])^(p+1)*
    Simp[a^2*(n+1)*(n+3)-b^2*(n+p+2)*(n+p+4)+a*b*(p+1)*Cos[c+d*x]-(a^2*(n+2)*(n+3)-b^2*(n+p+3)*(n+p+4))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && RationalQ[p] && p<-1 && Not[RationalQ[n] && n<-1] && NonzeroQ[n+p+4]


Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)/(a*d*(n+1)) - 
  b*(n+p+2)*Cos[c+d*x]*Sin[c+d*x]^(n+2)*(a+b*Sin[c+d*x])^(p+1)/(a^2*d*(n+1)*(n+2)) - 
  1/(a^2*(n+1)*(n+2))*Int[Sin[c+d*x]^(n+2)*(a+b*Sin[c+d*x])^p*
    Simp[a^2*n*(n+2)-b^2*(n+p+2)*(n+p+3)+a*b*p*Sin[c+d*x]-(a^2*(n+1)*(n+2)-b^2*(n+p+2)*(n+p+4))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[p] && p<-1] && RationalQ[n] && n<-1 && (n<-2 || ZeroQ[n+p+4])


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)/(a*d*(n+1)) + 
  b*(n+p+2)*Sin[c+d*x]*Cos[c+d*x]^(n+2)*(a+b*Cos[c+d*x])^(p+1)/(a^2*d*(n+1)*(n+2)) - 
  1/(a^2*(n+1)*(n+2))*Int[Cos[c+d*x]^(n+2)*(a+b*Cos[c+d*x])^p*
    Simp[a^2*n*(n+2)-b^2*(n+p+2)*(n+p+3)+a*b*p*Cos[c+d*x]-(a^2*(n+1)*(n+2)-b^2*(n+p+2)*(n+p+4))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[p] && p<-1] && RationalQ[n] && n<-1 && (n<-2 || ZeroQ[n+p+4])


Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)/(a*d*(n+1)) - 
  Cos[c+d*x]*Sin[c+d*x]^(2+n)*(a+b*Sin[c+d*x])^(p+1)/(b*d*(n+p+4)) + 
  1/(a*b*(n+1)*(n+p+4))*Int[Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^p*
    Simp[a^2*(n+1)*(n+2)-b^2*(n+p+2)*(n+p+4)+a*b*(p+3)*Sin[c+d*x]-(a^2*(n+1)*(n+3)-b^2*(n+p+3)*(n+p+4))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[p] && p<-1] && RationalQ[n] && n<-1 && NonzeroQ[n+p+4]


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)/(a*d*(n+1)) + 
  Sin[c+d*x]*Cos[c+d*x]^(2+n)*(a+b*Cos[c+d*x])^(p+1)/(b*d*(n+p+4)) + 
  1/(a*b*(n+1)*(n+p+4))*Int[Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^p*
    Simp[a^2*(n+1)*(n+2)-b^2*(n+p+2)*(n+p+4)+a*b*(p+3)*Cos[c+d*x]-(a^2*(n+1)*(n+3)-b^2*(n+p+3)*(n+p+4))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[p] && p<-1] && RationalQ[n] && n<-1 && NonzeroQ[n+p+4]


Int[cos[c_.+d_.*x_]^4*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  a*(n+3)*Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)/(b^2*d*(n+p+3)*(n+p+4)) - 
  Cos[c+d*x]*Sin[c+d*x]^(n+2)*(a+b*Sin[c+d*x])^(p+1)/(b*d*(n+p+4)) - 
  1/(b^2*(n+p+3)*(n+p+4))*Int[Sin[c+d*x]^n*(a+b*Sin[c+d*x])^p*
    Simp[a^2*(n+1)*(n+3)-b^2*(n+p+3)*(n+p+4)+a*b*p*Sin[c+d*x]-(a^2*(n+2)*(n+3)-b^2*(n+p+3)*(n+p+5))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n,p},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[p] && p<-1] && Not[RationalQ[n] && n<-1] && NonzeroQ[n+p+3] && NonzeroQ[n+p+4]


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -a*(n+3)*Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)/(b^2*d*(n+p+3)*(n+p+4)) + 
  Sin[c+d*x]*Cos[c+d*x]^(n+2)*(a+b*Cos[c+d*x])^(p+1)/(b*d*(n+p+4)) - 
  1/(b^2*(n+p+3)*(n+p+4))*Int[Cos[c+d*x]^n*(a+b*Cos[c+d*x])^p*
    Simp[a^2*(n+1)*(n+3)-b^2*(n+p+3)*(n+p+4)+a*b*p*Cos[c+d*x]-(a^2*(n+2)*(n+3)-b^2*(n+p+3)*(n+p+5))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n,p},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[p] && p<-1] && Not[RationalQ[n] && n<-1] && NonzeroQ[n+p+3] && NonzeroQ[n+p+4]


Int[cos[c_.+d_.*x_]^6*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Cos[c+d*x]*Sin[c+d*x]^(n+1)*(a+b*Sin[c+d*x])^(p+1)/(a*d*(n+1)) - 
  b*(n+p+2)*Cos[c+d*x]*Sin[c+d*x]^(n+2)*(a+b*Sin[c+d*x])^(p+1)/(a^2*d*(n+1)*(n+2)) - 
  a*(n+5)*Cos[c+d*x]*Sin[c+d*x]^(n+3)*(a+b*Sin[c+d*x])^(p+1)/(b^2*d*(n+p+5)*(n+p+6)) + 
  Cos[c+d*x]*Sin[c+d*x]^(n+4)*(a+b*Sin[c+d*x])^(p+1)/(b*d*(n+p+6)) + 
  1/(a^2*b^2*(n+1)*(n+2)*(n+p+5)*(n+p+6))*Int[Sin[c+d*x]^(n+2)*(a+b*Sin[c+d*x])^p*Simp[
    a^4*(n+1)*(n+2)*(n+3)*(n+5)-a^2*b^2*(n+2)*(2*n+1)*(n+p+5)*(n+p+6)+b^4*(n+p+2)*(n+p+3)*(n+p+5)*(n+p+6) + 
    a*b*p*(a^2*(n+1)*(n+2)-b^2*(n+p+5)*(n+p+6))*Sin[c+d*x] - 
    (a^4*(n+1)*(n+2)*(4+n)*(n+5)+b^4*(n+p+2)*(n+p+4)*(n+p+5)*(n+p+6)-a^2*b^2*(n+1)*(n+2)*(n+p+5)*(2*n+2*p+13))*Sin[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n,p},x] && NonzeroQ[a^2-b^2] && NonzeroQ[n+1] && NonzeroQ[n+2] && NonzeroQ[n+p+5] && NonzeroQ[n+p+6] && Not[PositiveIntegerQ[p]]


Int[sin[c_.+d_.*x_]^6*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  -Sin[c+d*x]*Cos[c+d*x]^(n+1)*(a+b*Cos[c+d*x])^(p+1)/(a*d*(n+1)) + 
  b*(n+p+2)*Sin[c+d*x]*Cos[c+d*x]^(n+2)*(a+b*Cos[c+d*x])^(p+1)/(a^2*d*(n+1)*(n+2)) + 
  a*(n+5)*Sin[c+d*x]*Cos[c+d*x]^(n+3)*(a+b*Cos[c+d*x])^(p+1)/(b^2*d*(n+p+5)*(n+p+6)) - 
  Sin[c+d*x]*Cos[c+d*x]^(n+4)*(a+b*Cos[c+d*x])^(p+1)/(b*d*(n+p+6)) + 
  1/(a^2*b^2*(n+1)*(n+2)*(n+p+5)*(n+p+6))*Int[Cos[c+d*x]^(n+2)*(a+b*Cos[c+d*x])^p*Simp[
    a^4*(n+1)*(n+2)*(n+3)*(n+5)-a^2*b^2*(n+2)*(2*n+1)*(n+p+5)*(n+p+6)+b^4*(n+p+2)*(n+p+3)*(n+p+5)*(n+p+6) + 
    a*b*p*(a^2*(n+1)*(n+2)-b^2*(n+p+5)*(n+p+6))*Cos[c+d*x] - 
    (a^4*(n+1)*(n+2)*(4+n)*(n+5)+b^4*(n+p+2)*(n+p+4)*(n+p+5)*(n+p+6)-a^2*b^2*(n+1)*(n+2)*(n+p+5)*(2*n+2*p+13))*Cos[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,n,p},x] && NonzeroQ[a^2-b^2] && NonzeroQ[n+1] && NonzeroQ[n+2] && NonzeroQ[n+p+5] && NonzeroQ[n+p+6] && Not[PositiveIntegerQ[p]]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n,(a+b*sin[c+d*x])^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && PositiveIntegerQ[p]


Int[sin[c_.+d_.*x_]^m_.*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[ExpandTrig[sin[c+d*x]^m*cos[c+d*x]^n,(a+b*cos[c+d*x])^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && PositiveIntegerQ[p]


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -a*Cos[c+d*x]^(m-1)/(b^2*d*(m-1)) - 
  1/b*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]^2,x] - 
  (a^2-b^2)/b^2*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[m]] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[cos[c_.+d_.*x_]*sin[c_.+d_.*x_]^n_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  a*Sin[c+d*x]^(n-1)/(b^2*d*(n-1)) - 
  1/b*Int[Cos[c+d*x]^2*Sin[c+d*x]^(n-2),x] - 
  (a^2-b^2)/b^2*Int[Cos[c+d*x]*Sin[c+d*x]^(n-2)/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[n]] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -a*Cos[c+d*x]^(m+1)/(d*(m+1)*(a^2-b^2)) - 
  b/(a^2-b^2)*Int[Cos[c+d*x]^m*Sin[c+d*x]^2,x] - 
  b^2/(a^2-b^2)*Int[Cos[c+d*x]^(m+2)*Sin[c+d*x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[m]] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]*sin[c_.+d_.*x_]^n_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  a*Sin[c+d*x]^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  b/(a^2-b^2)*Int[Cos[c+d*x]^2*Sin[c+d*x]^n,x] - 
  b^2/(a^2-b^2)*Int[Cos[c+d*x]*Sin[c+d*x]^(n+2)/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[n]] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n/(a+b*sin[c+d*x]),x],x] /;
FreeQ[{a,b,c,d},x] && EvenQ[m] && NonzeroQ[a^2-b^2] && IntegerQ[n] && n>1 && m>1


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n/(a+b*cos[c+d*x]),x],x] /;
FreeQ[{a,b,c,d},x] && EvenQ[n] && NonzeroQ[a^2-b^2] && IntegerQ[m] && m>1 && n>1


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  a/(a^2-b^2)*Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-2),x] - 
  b/(a^2-b^2)*Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1),x] - 
  a^2/(a^2-b^2)*Int[Cos[c+d*x]^(m+2)*Sin[c+d*x]^(n-2)/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[m]] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  a/(a^2-b^2)*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]^n,x] - 
  b/(a^2-b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n,x] - 
  a^2/(a^2-b^2)*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]^(n+2)/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[n]] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>1 && n<-1


Int[cos[c_.+d_.*x_]^m_/(sin[c_.+d_.*x_]*(a_+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[Cos[c+d*x]^m/Sin[c+d*x],x] - b/a*Int[Cos[c+d*x]^m/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[m]] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[sin[c_.+d_.*x_]^m_/(cos[c_.+d_.*x_]*(a_+b_.*cos[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[Sin[c+d*x]^m/Cos[c+d*x],x] - b/a*Int[Sin[c+d*x]^m/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[m]] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]^n,x] - 
  b/a^2*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]^(n+1),x] - 
  (a^2-b^2)/a^2*Int[Cos[c+d*x]^(m-2)*Sin[c+d*x]^(n+2)/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[m]] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<0 && m>1


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_/(a_+b_.*cos[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-2),x] - 
  b/a^2*Int[Cos[c+d*x]^(m+1)*Sin[c+d*x]^(n-2),x] - 
  (a^2-b^2)/a^2*Int[Cos[c+d*x]^(m+2)*Sin[c+d*x]^(n-2)/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && Not[OddQ[n]] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<0 && n>1


Int[cos[c_.+d_.*x_]^6*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[Sin[c+d*x]^n*(1-3*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^p,x] + 
  Int[Sin[c+d*x]^(n+4)*(3-Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && IntegerQ[p+1/2]


Int[sin[c_.+d_.*x_]^4*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[Cos[c+d*x]^n*(1-3*Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^p,x] + 
  Int[Cos[c+d*x]^(n+4)*(3-Cos[c+d*x]^2)*(a+b*Cos[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && IntegerQ[p+1/2]


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[ExpandTrig[sin[c+d*x]^n*(1-sin[c+d*x]^2)^(m/2)*(a+b*sin[c+d*x])^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && IntegerQ[p+1/2] && PositiveIntegerQ[m/2]


Int[sin[c_.+d_.*x_]^m_*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^n*(1-cos[c+d*x]^2)^(m/2)*(a+b*cos[c+d*x])^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && IntegerQ[p+1/2] && PositiveIntegerQ[m/2]


Int[cos[c_.+d_.*x_]^m_*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[ExpandTrig[sin[c+d*x]^n*(a+b*sin[c+d*x])^p*(1-sin[c+d*x]^2)^(m/2),x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && IntegerQ[p] && p<-1 && EvenQ[m]


Int[sin[c_.+d_.*x_]^m_*cos[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^n*(a+b*cos[c+d*x])^p*(1-cos[c+d*x]^2)^(m/2),x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && IntegerQ[p] && p<-1 && EvenQ[m]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Module[{v=ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n*(a+b*sin[c+d*x])^p,x]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_,x_Symbol] :=
  Module[{v=ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n*(a+b*cos[c+d*x])^p,x]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*sin[c_.+d_.*x_])^p_.,x_Symbol] :=
  Defer[Int][cos[c+d*x]^m*sin[c+d*x]^n*(a+b*sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_+b_.*cos[c_.+d_.*x_])^p_.,x_Symbol] :=
  Defer[Int][cos[c+d*x]^m*sin[c+d*x]^n*(a+b*cos[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[u_.*(e_*sin[c_.+d_.*x_])^m_*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m/Sin[c+d*x]^m*Int[ActivateTrig[u]*Sin[c+d*x]^m*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_*cos[c_.+d_.*x_])^m_*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m/Cos[c+d*x]^m*Int[ActivateTrig[u]*Cos[c+d*x]^m*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_*cos[c_.+d_.*x_])^m_*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m/Cos[c+d*x]^m*Int[ActivateTrig[u]*Cos[c+d*x]^m*(a+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_*sin[c_.+d_.*x_])^m_*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m/Sin[c+d*x]^m*Int[ActivateTrig[u]*Sin[c+d*x]^m*(a+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_.*tan[c_.+d_.*x_])^m_*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Cos[c+d*x]^m*(e*Tan[c+d*x])^m/Sin[c+d*x]^m*Int[ActivateTrig[u]*Sin[c+d*x]^m*(a+b*Sin[c+d*x])^n/Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Sin[c+d*x]^m*(e*Cot[c+d*x])^m/Cos[c+d*x]^m*Int[ActivateTrig[u]*Cos[c+d*x]^m*(a+b*Cos[c+d*x])^n/Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Sin[c+d*x]^m*(e*Cot[c+d*x])^m/Cos[c+d*x]^m*Int[ActivateTrig[u]*Cos[c+d*x]^m*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_.*tan[c_.+d_.*x_])^m_*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Cos[c+d*x]^m*(e*Tan[c+d*x])^m/Sin[c+d*x]^m*Int[ActivateTrig[u]*Sin[c+d*x]^m*(a+b*Cos[c+d*x])^n/Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_.*sec[c_.+d_.*x_])^m_*(a_+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Cos[c+d*x]^m*(e*Sec[c+d*x])^m*Int[ActivateTrig[u]*(a+b*Sin[c+d*x])^n/Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_.*csc[c_.+d_.*x_])^m_*(a_+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Sin[c+d*x]^m*(e*Csc[c+d*x])^m*Int[ActivateTrig[u]*(a+b*Cos[c+d*x])^n/Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_.*csc[c_.+d_.*x_])^m_*(a_.+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m*Sin[c+d*x]^m*Int[ActivateTrig[u]*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[u_.*(e_.*sec[c_.+d_.*x_])^m_*(a_.+b_.*cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m*Cos[c+d*x]^m*Int[ActivateTrig[u]*(a+b*Cos[c+d*x])^n/Cos[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


(* ::Subsection::Closed:: *)
(*7.2.1 tan(c+d x)^m (a+b tan(c+d x))^n*)


Int[tan[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  b*Tan[c+d*x]^m/(d*m) - Int[Tan[c+d*x]^(m-1)*(b-a*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -b*Cot[c+d*x]^m/(d*m) - Int[Cot[c+d*x]^(m-1)*(b-a*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[(a_+b_.*tan[c_.+d_.*x_])/tan[c_.+d_.*x_],x_Symbol] :=
  b*x + a*Int[1/Tan[c + d*x], x] /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*cot[c_.+d_.*x_])/cot[c_.+d_.*x_],x_Symbol] :=
  b*x + a*Int[1/Cot[c + d*x], x] /;
FreeQ[{a,b,c,d},x]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a*Tan[c+d*x]^(m+1)/(d*(m+1)) + Int[Tan[c+d*x]^(m+1)*(b-a*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -a*Cot[c+d*x]^(m+1)/(d*(m+1)) + Int[Cot[c+d*x]^(m+1)*(b-a*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1


Int[(a_+b_.*tan[c_.+d_.*x_])/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
(*Sqrt[2]*(a+b)/d*ArcTan[(a-b)*Sqrt[Tan[c+d*x]]/(Sqrt[2]*a)] *)
  Sqrt[2]*(a-b)/d*ArcTanh[(a+b)*Sqrt[Tan[c+d*x]]/(Sqrt[2]*a)] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[(a_+b_.*cot[c_.+d_.*x_])/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
(*-Sqrt[2]*(a+b)/d*ArcTan[(a-b)*Sqrt[Cot[c+d*x]]/(Sqrt[2]*a)] *)
  -Sqrt[2]*(a-b)/d*ArcTanh[(a+b)*Sqrt[Cot[c+d*x]]/(Sqrt[2]*a)] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a^2/d*Subst[Int[x^m/(a-b*x),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && -1<m<0


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -a^2/d*Subst[Int[x^m/(a-b*x),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && -1<m<0


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a*Tan[c+d*x]^(m+1)/(d*(m+1))*Hypergeometric2F1[1,m+1,m+2,b*Tan[c+d*x]/a] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -a*Cot[c+d*x]^(m+1)/(d*(m+1))*Hypergeometric2F1[1,m+1,m+2,b*Cot[c+d*x]/a] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2]


Int[(a_+b_.*tan[c_.+d_.*x_])/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
(*Sqrt[2]*a/d*ArcTan[Sqrt[2]*Sqrt[Tan[c+d*x]]/(1-Tan[c+d*x])] *)
  Sqrt[2]*a*ArcTan[1+Sqrt[2]*Sqrt[Tan[c+d*x]]]/d - Sqrt[2]*a*ArcTan[1-Sqrt[2]*Sqrt[Tan[c+d*x]]]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b]


Int[(a_+b_.*cot[c_.+d_.*x_])/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
(*-Sqrt[2]*a/d*ArcTan[Sqrt[2]*Sqrt[Cot[c+d*x]]/(1-Cot[c+d*x])] *)
  -Sqrt[2]*a*ArcTan[1+Sqrt[2]*Sqrt[Cot[c+d*x]]]/d + Sqrt[2]*a*ArcTan[1-Sqrt[2]*Sqrt[Cot[c+d*x]]]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b]


Int[(a_+b_.*tan[c_.+d_.*x_])/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
  a*Log[1+Sqrt[2]*Sqrt[Tan[c+d*x]]+Tan[c+d*x]]/(Sqrt[2]*d) - 
  a*Log[1-Sqrt[2]*Sqrt[Tan[c+d*x]]+Tan[c+d*x]]/(Sqrt[2]*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b]


Int[(a_+b_.*cot[c_.+d_.*x_])/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
  -a*Log[1+Sqrt[2]*Sqrt[Cot[c+d*x]]+Cot[c+d*x]]/(Sqrt[2]*d) + 
  a*Log[1-Sqrt[2]*Sqrt[Cot[c+d*x]]+Cot[c+d*x]]/(Sqrt[2]*d) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  (a+I*b)/2*Int[Tan[c+d*x]^m*(1-I*Tan[c+d*x]),x] + 
  (a-I*b)/2*Int[Tan[c+d*x]^m*(1+I*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  (a+I*b)/2*Int[Cot[c+d*x]^m*(1-I*Cot[c+d*x]),x] + 
  (a-I*b)/2*Int[Cot[c+d*x]^m*(1+I*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^2/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  Log[RemoveContent[a+b*Tan[c+d*x],x]]/(b*d) - Int[1/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[cot[c_.+d_.*x_]^2/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -Log[RemoveContent[a+b*Cot[c+d*x],x]]/(b*d) - Int[1/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[tan[c_.+d_.*x_]^2*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) - 
  1/(a^2+b^2)*Int[(a-b*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[cot[c_.+d_.*x_]^2*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) - 
  1/(a^2+b^2)*Int[(a-b*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[tan[c_.+d_.*x_]^2*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) - Int[(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[n+1]


Int[cot[c_.+d_.*x_]^2*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) - Int[(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[n+1]


Int[(a_+b_.*tan[c_.+d_.*x_])^2/tan[c_.+d_.*x_],x_Symbol] :=
  2*a*b*x + a^2*Int[Cot[c+d*x],x] + b^2*Int[Tan[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*cot[c_.+d_.*x_])^2/cot[c_.+d_.*x_],x_Symbol] :=
  2*a*b*x + a^2*Int[Tan[c+d*x],x] + b^2*Int[Cot[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^2,x_Symbol] :=
  a^2*Tan[c+d*x]^(m+1)/(d*(m+1)) + Int[Tan[c+d*x]^(m+1)*(2*a*b-(a^2-b^2)*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^2,x_Symbol] :=
  -a^2*Cot[c+d*x]^(m+1)/(d*(m+1)) + Int[Cot[c+d*x]^(m+1)*(2*a*b-(a^2-b^2)*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^2,x_Symbol] :=
  b^2*Tan[c+d*x]^(m+1)/(d*(m+1)) + Int[Tan[c+d*x]^m*(a^2-b^2+2*a*b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,m},x] && Not[RationalQ[m] && m<=-1]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^2,x_Symbol] :=
  -b^2*Cot[c+d*x]^(m+1)/(d*(m+1)) + Int[Cot[c+d*x]^m*(a^2-b^2+2*a*b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,m},x] && Not[RationalQ[m] && m<=-1]


Int[1/(tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[1/Tan[c+d*x],x] - b/a*Int[1/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[1/(cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[1/Cot[c+d*x],x] - b/a*Int[1/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (a+b*Tan[c+d*x])^n/(2*d*n) + 1/(2*b)*Int[(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a+b*Cot[c+d*x])^n/(2*d*n) + 1/(2*b)*Int[(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (a+b*Tan[c+d*x])^n/(d*n) - b/a*Int[(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && Not[RationalQ[n] && n<0]


Int[cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a+b*Cot[c+d*x])^n/(d*n) - b/a*Int[(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && Not[RationalQ[n] && n<0]


Int[Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -b/a*Int[Sqrt[a+b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]],x] - 
  1/b*Int[(a-b*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -b/a*Int[Sqrt[a+b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]],x] - 
  1/b*Int[(a-b*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


(* Int[tan[c_.+d_.*x_]^m_*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -b/a*Int[Tan[c+d*x]^(m-1)*Sqrt[a+b*Tan[c+d*x]],x] - 
  1/b*Int[Tan[c+d*x]^(m-1)*(a-b*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && 0<m<1 *)


(* Int[cot[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -b/a*Int[Cot[c+d*x]^(m-1)*Sqrt[a+b*Cot[c+d*x]],x] - 
  1/b*Int[Cot[c+d*x]^(m-1)*(a-b*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && 0<m<1 *)


Int[tan[c_.+d_.*x_]^m_*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  2*Tan[c+d*x]^(m-1)*Sqrt[a+b*Tan[c+d*x]]/(d*(2*m-1)) - 
  1/(a*(2*m-1))*Int[Tan[c+d*x]^(m-2)*(2*a*(m-1)+b*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -2*Cot[c+d*x]^(m-1)*Sqrt[a+b*Cot[c+d*x]]/(d*(2*m-1)) - 
  1/(a*(2*m-1))*Int[Cot[c+d*x]^(m-2)*(2*a*(m-1)+b*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]]/tan[c_.+d_.*x_],x_Symbol] :=
  b/a*Int[Sqrt[a+b*Tan[c+d*x]],x] + 
  1/a*Int[(a-b*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]]/Tan[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]]/cot[c_.+d_.*x_],x_Symbol] :=
  b/a*Int[Sqrt[a+b*Cot[c+d*x]],x] + 
  1/a*Int[(a-b*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]]/Cot[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]]/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*a/(Rt[b,2]*d)*ArcTanh[Sqrt[2]*Rt[b,2]*Sqrt[Tan[c+d*x]]/Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && PosQ[b]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]]/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*a/(Rt[b,2]*d)*ArcTanh[Sqrt[2]*Rt[b,2]*Sqrt[Cot[c+d*x]]/Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && PosQ[b]


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]]/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*a/(Rt[-b,2]*d)*ArcTan[Sqrt[2]*Rt[-b,2]*Sqrt[Tan[c+d*x]]/Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && NegQ[b]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]]/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*a/(Rt[-b,2]*d)*ArcTan[Sqrt[2]*Rt[-b,2]*Sqrt[Cot[c+d*x]]/Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && NegQ[b]


Int[tan[c_.+d_.*x_]^m_*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  Tan[c+d*x]^(m+1)*Sqrt[a+b*Tan[c+d*x]]/(d*(m+1)) - 
  1/(2*a*(m+1))*Int[Tan[c+d*x]^(m+1)*(b+a*(2*m+3)*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Cot[c+d*x]^(m+1)*Sqrt[a+b*Cot[c+d*x]]/(d*(m+1)) - 
  1/(2*a*(m+1))*Int[Cot[c+d*x]^(m+1)*(b+a*(2*m+3)*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-2)/(d*(m+n-1)) + 
  a/(m+n-1)*Int[Tan[c+d*x]^m*(a*(2*m+n)+b*(2*m+3*n-4)*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m>0 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-2)/(d*(m+n-1)) + 
  a/(m+n-1)*Int[Cot[c+d*x]^m*(a*(2*m+n)+b*(2*m+3*n-4)*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m>0 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(a_+b_.*tan[c_.+d_.*x_])^(3/2)/tan[c_.+d_.*x_],x_Symbol] :=
  2*b*Int[Sqrt[a+b*Tan[c+d*x]],x] + Int[(a-b*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]]/Tan[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[(a_+b_.*cot[c_.+d_.*x_])^(3/2)/cot[c_.+d_.*x_],x_Symbol] :=
  2*b*Int[Sqrt[a+b*Cot[c+d*x]],x] + Int[(a-b*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]]/Cot[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[(a_+b_.*tan[c_.+d_.*x_])^(3/2)/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
  2*a*Int[Sqrt[a+b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]],x] + 
  b/a*Int[(b+a*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[(a_+b_.*cot[c_.+d_.*x_])^(3/2)/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
  2*a*Int[Sqrt[a+b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]],x] + 
  b/a*Int[(b+a*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(a+b*Tan[c+d*x])^(n-1)/(d*(n-1)*Tan[c+d*x]^(n-1)) + 
  2*b*Int[(a+b*Tan[c+d*x])^(n-1)/Tan[c+d*x]^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m+n==0


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a+b*Cot[c+d*x])^(n-1)/(d*(n-1)*Cot[c+d*x]^(n-1)) + 
  2*b*Int[(a+b*Cot[c+d*x])^(n-1)/Cot[c+d*x]^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m+n==0


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a+b*Tan[c+d*x])^n/(d*n*Tan[c+d*x]^n) + b/a*Int[(a+b*Tan[c+d*x])^n/Tan[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m+n+1==0


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (a+b*Cot[c+d*x])^n/(d*n*Cot[c+d*x]^n) + b/a*Int[(a+b*Cot[c+d*x])^n/Cot[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m+n+1==0


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-2)/(d*(m+1)) + 
  a/(m+1)*Int[Tan[c+d*x]^(m+1)*(b*(2*m-n+4)-a*(2*m+n)*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-2)/(d*(m+1)) + 
  a/(m+1)*Int[Cot[c+d*x]^(m+1)*(b*(2*m-n+4)-a*(2*m+n)*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-2)/(d*(m+n-1)) + 
  a/(m+n-1)*Int[Tan[c+d*x]^m*(a*(2*m+n)+b*(2*m+3*n-4)*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n>2 && NonzeroQ[m+n-1] && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-2)/(d*(m+n-1)) + 
  a/(m+n-1)*Int[Cot[c+d*x]^m*(a*(2*m+n)+b*(2*m+3*n-4)*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n>2 && NonzeroQ[m+n-1] && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[Sqrt[tan[c_.+d_.*x_]]/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  b*Sqrt[Tan[c+d*x]]/(2*a*d*(a+b*Tan[c+d*x])) + 
  1/(4*a*b)*Int[(a+b*Tan[c+d*x])/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[Sqrt[cot[c_.+d_.*x_]]/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -b*Sqrt[Cot[c+d*x]]/(2*a*d*(a+b*Cot[c+d*x])) + 
  1/(4*a*b)*Int[(a+b*Cot[c+d*x])/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  -Tan[c+d*x]^(m-1)/(2*d*(a+b*Tan[c+d*x])) + 
  1/(2*a*b)*Int[Tan[c+d*x]^(m-2)*(b*(m-1)+a*m*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m>1


Int[cot[c_.+d_.*x_]^m_/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  Cot[c+d*x]^(m-1)/(2*d*(a+b*Cot[c+d*x])) + 
  1/(2*a*b)*Int[Cot[c+d*x]^(m-2)*(b*(m-1)+a*m*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m>1


Int[tan[c_.+d_.*x_]^m_/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  Tan[c+d*x]^(m+1)/(2*d*(a+b*Tan[c+d*x])) - 
  1/(2*a*b)*Int[Tan[c+d*x]^m*(b*(m-1)+a*m*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]^m_/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -Cot[c+d*x]^(m+1)/(2*d*(a+b*Cot[c+d*x])) - 
  1/(2*a*b)*Int[Cot[c+d*x]^m*(b*(m-1)+a*m*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2]


Int[Sqrt[tan[c_.+d_.*x_]]/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  b*Sqrt[Tan[c+d*x]]/(a*d*Sqrt[a+b*Tan[c+d*x]]) + 
  1/(2*b)*Int[Sqrt[a+b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[Sqrt[cot[c_.+d_.*x_]]/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -b*Sqrt[Cot[c+d*x]]/(a*d*Sqrt[a+b*Cot[c+d*x]]) + 
  1/(2*b)*Int[Sqrt[a+b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[Tan[c+d*x]]/(d*Sqrt[a+b*Tan[c+d*x]]) + 
  1/(2*a^2)*Int[(a-2*b*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[Cot[c+d*x]]/(d*Sqrt[a+b*Cot[c+d*x]]) + 
  1/(2*a^2)*Int[(a-2*b*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[1/(tan[c_.+d_.*x_]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  1/(d*Sqrt[a+b*Tan[c+d*x]]) + 
  1/(2*a^2)*Int[(2*a-b*Tan[c+d*x])*Sqrt[a+b*Tan[c+d*x]]/Tan[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[1/(cot[c_.+d_.*x_]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  -1/(d*Sqrt[a+b*Cot[c+d*x]]) + 
  1/(2*a^2)*Int[(2*a-b*Cot[c+d*x])*Sqrt[a+b*Cot[c+d*x]]/Cot[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[1/(Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  Sqrt[Tan[c+d*x]]/(d*Sqrt[a+b*Tan[c+d*x]]) + 
  1/(2*a)*Int[Sqrt[a+b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[1/(Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  -Sqrt[Cot[c+d*x]]/(d*Sqrt[a+b*Cot[c+d*x]]) + 
  1/(2*a)*Int[Sqrt[a+b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  Tan[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Tan[c+d*x]]) + 
  1/(2*a*(m+1))*Int[Tan[c+d*x]^(m+1)*(b-a*(2*m+1)*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Cot[c+d*x]^(m+1)/(d*(m+1)*Sqrt[a+b*Cot[c+d*x]]) + 
  1/(2*a*(m+1))*Int[Cot[c+d*x]^(m+1)*(b-a*(2*m+1)*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[Sqrt[tan[c_.+d_.*x_]]*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Sqrt[Tan[c+d*x]]*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  1/(4*a^2*n)*Int[(b+a*(2*n+1)*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1)/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[Sqrt[cot[c_.+d_.*x_]]*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sqrt[Cot[c+d*x]]*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  1/(4*a^2*n)*Int[(b+a*(2*n+1)*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1)/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a+b*Tan[c+d*x])^n/(2*a*d*n*Tan[c+d*x]^n) - 
  b/(2*a^2)*Int[(a+b*Tan[c+d*x])^(n+1)/Tan[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m+n==0


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a+b*Cot[c+d*x])^n/(2*a*d*n*Cot[c+d*x]^n) - 
  b/(2*a^2)*Int[(a+b*Cot[c+d*x])^(n+1)/Cot[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m+n==0


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a+b*Tan[c+d*x])^n/(2*d*n*Tan[c+d*x]^n) + 
  1/(2*a)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m+n+1==0


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (a+b*Cot[c+d*x])^n/(2*d*n*Cot[c+d*x]^n) + 
  1/(2*a)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m+n+1==0


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  Tan[c+d*x]^(m-1)*(a+b*Tan[c+d*x])^n/(2*d*n) - 
  1/(2*a^2*n)*Int[Tan[c+d*x]^(m-2)*(a*(m-1)-b*(m-n-1)*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]^(m-1)*(a+b*Cot[c+d*x])^n/(2*d*n) - 
  1/(2*a^2*n)*Int[Cot[c+d*x]^(m-2)*(a*(m-1)-b*(m-n-1)*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(2*d*n) + 
  1/(2*a^2*n)*Int[Tan[c+d*x]^m*(a*(m+2*n+1)-b*(m+n+1)*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(2*d*n) + 
  1/(2*a^2*n)*Int[Cot[c+d*x]^m*(a*(m+2*n+1)-b*(m+n+1)*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  Tan[c+d*x]^(m-1)*(a+b*Tan[c+d*x])^n/(d*(m+n-1)) - 
  1/(a*(m+n-1))*Int[Tan[c+d*x]^(m-2)*(a*(m-1)+b*n*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]^(m-1)*(a+b*Cot[c+d*x])^n/(d*(m+n-1)) - 
  1/(a*(m+n-1))*Int[Cot[c+d*x]^(m-2)*(a*(m-1)+b*n*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*tan[c_.+d_.*x_])^n_/tan[c_.+d_.*x_],x_Symbol] :=
  b/a*Int[(a+b*Tan[c+d*x])^n,x] + 
  1/a*Int[(a-b*Tan[c+d*x])*(a+b*Tan[c+d*x])^n/Tan[c+d*x],x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2]


Int[(a_+b_.*cot[c_.+d_.*x_])^n_/cot[c_.+d_.*x_],x_Symbol] :=
  b/a*Int[(a+b*Cot[c+d*x])^n,x] + 
  1/a*Int[(a-b*Cot[c+d*x])*(a+b*Cot[c+d*x])^n/Cot[c+d*x],x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+1)) - 
  1/(a*(m+1))*Int[Tan[c+d*x]^(m+1)*(b*n+a*(m+n+1)*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1 && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+1)) - 
  1/(a*(m+1))*Int[Cot[c+d*x]^(m+1)*(b*n+a*(m+n+1)*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1 && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-1)/(d*(m+1)*((a+b*Tan[c+d*x])/a)^(n-1))*
    AppellF1[m+1,1-n,1,m+2,-b*Tan[c+d*x]/a,b*Tan[c+d*x]/a] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-1)/(d*(m+1)*((a+b*Cot[c+d*x])/a)^(n-1))*
    AppellF1[m+1,1-n,1,m+2,-b*Cot[c+d*x]/a,b*Cot[c+d*x]/a] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[tan[c_.+d_.*x_]*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -Int[(b-a*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] + 
  b*Int[(1+Tan[c+d*x]^2)/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Int[(b-a*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] + 
  b*Int[(1+Cot[c+d*x]^2)/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -Int[(b-a*Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] + 
  b*Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Int[(b-a*Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] + 
  b*Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  2*Tan[c+d*x]^(m-1)*Sqrt[a+b*Tan[c+d*x]]/(d*(2*m-1)) - 
  1/(2*m-1)*Int[Tan[c+d*x]^(m-2)/Sqrt[a+b*Tan[c+d*x]]*(2*a*(m-1)+b*(2*m-1)*Tan[c+d*x]-a*Tan[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -2*Cot[c+d*x]^(m-1)*Sqrt[a+b*Cot[c+d*x]]/(d*(2*m-1)) - 
  1/(2*m-1)*Int[Cot[c+d*x]^(m-2)/Sqrt[a+b*Cot[c+d*x]]*(2*a*(m-1)+b*(2*m-1)*Cot[c+d*x]-a*Cot[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[Sqrt[a_+b_.*tan[c_.+d_.*x_]]/tan[c_.+d_.*x_],x_Symbol] :=
  Int[(b-a*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] + 
  a*Int[(1+Tan[c+d*x]^2)/(Tan[c+d*x]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[a_+b_.*cot[c_.+d_.*x_]]/cot[c_.+d_.*x_],x_Symbol] :=
  Int[(b-a*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] + 
  a*Int[(1+Cot[c+d*x]^2)/(Cot[c+d*x]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  Tan[c+d*x]^(m+1)*Sqrt[a+b*Tan[c+d*x]]/(d*(m+1)) - 
  1/(2*(m+1))*Int[Tan[c+d*x]^(m+1)/Sqrt[a+b*Tan[c+d*x]]*(b+2*a*(m+1)*Tan[c+d*x]+b*(2*m+3)*Tan[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Cot[c+d*x]^(m+1)*Sqrt[a+b*Cot[c+d*x]]/(d*(m+1)) - 
  1/(2*(m+1))*Int[Cot[c+d*x]^(m+1)/Sqrt[a+b*Cot[c+d*x]]*(b+2*a*(m+1)*Cot[c+d*x]+b*(2*m+3)*Cot[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[tan[c_.+d_.*x_]^m_*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -(I*a+b)/2*Int[Tan[c+d*x]^m*(I-Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] - 
  (I*a-b)/2*Int[Tan[c+d*x]^m*(I+Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)]


Int[cot[c_.+d_.*x_]^m_*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -(I*a+b)/2*Int[Cot[c+d*x]^m*(I-Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] - 
  (I*a-b)/2*Int[Cot[c+d*x]^m*(I+Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)]


Int[tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (a+b*Tan[c+d*x])^n/(d*n) - Int[(b-a*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a+b*Cot[c+d*x])^n/(d*n) - Int[(b-a*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^(3/2),x_Symbol] :=
  2*b*Tan[c+d*x]^m*Sqrt[a+b*Tan[c+d*x]]/(d*(2*m+1)) - 
  1/(2*m+1)*Int[Tan[c+d*x]^(m-1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[2*a*b*m-(a^2-b^2)*(2*m+1)*Tan[c+d*x]-2*a*b*(m+1)*Tan[c+d*x]^2,x], x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*b*Cot[c+d*x]^m*Sqrt[a+b*Cot[c+d*x]]/(d*(2*m+1)) - 
  1/(2*m+1)*Int[Cot[c+d*x]^(m-1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[2*a*b*m-(a^2-b^2)*(2*m+1)*Cot[c+d*x]-2*a*b*(m+1)*Cot[c+d*x]^2,x], x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0 && IntegerQ[2*m]


Int[(a_+b_.*tan[c_.+d_.*x_])^(3/2)/tan[c_.+d_.*x_],x_Symbol] :=
  Int[Simp[2*a*b-(a^2-b^2)*Tan[c+d*x],x]/Sqrt[a+b*Tan[c+d*x]],x] + 
  a^2*Int[(1+Tan[c+d*x]^2)/(Tan[c+d*x]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[(a_+b_.*cot[c_.+d_.*x_])^(3/2)/cot[c_.+d_.*x_],x_Symbol] :=
  Int[Simp[2*a*b-(a^2-b^2)*Cot[c+d*x],x]/Sqrt[a+b*Cot[c+d*x]],x] + 
  a^2*Int[(1+Cot[c+d*x]^2)/(Cot[c+d*x]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[(a_+b_.*tan[c_.+d_.*x_])^(3/2)/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
  Int[(a^2-b^2+2*a*b*Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] + 
  b^2*Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[(a_+b_.*cot[c_.+d_.*x_])^(3/2)/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
  Int[(a^2-b^2+2*a*b*Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] + 
  b^2*Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^(3/2),x_Symbol] :=
  a*Tan[c+d*x]^(m+1)*Sqrt[a+b*Tan[c+d*x]]/(d*(m+1)) + 
  1/(2*(m+1))*Int[(Tan[c+d*x]^(m+1)/Sqrt[a+b*Tan[c+d*x]])*
    Simp[a*b*(2*m+1)-2*(a^2-b^2)*(m+1)*Tan[c+d*x]-a*b*(2*m+3)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -a*Cot[c+d*x]^(m+1)*Sqrt[a+b*Cot[c+d*x]]/(d*(m+1)) + 
  1/(2*(m+1))*Int[(Cot[c+d*x]^(m+1)/Sqrt[a+b*Cot[c+d*x]])*
    Simp[a*b*(2*m+1)-2*(a^2-b^2)*(m+1)*Cot[c+d*x]-a*b*(2*m+3)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-2)/(d*(m+1)) + 
  1/(m+1)*Int[Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-3)*
    Simp[a^2*b*(2*m-n+4)-a*(a^2-3*b^2)*(m+1)*Tan[c+d*x]-b*(a^2*(m+n-1)-b^2*(m+1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>2 && m<-1


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-2)/(d*(m+1)) + 
  1/(m+1)*Int[Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-3)*
    Simp[a^2*b*(2*m-n+4)-a*(a^2-3*b^2)*(m+1)*Cot[c+d*x]-b*(a^2*(m+n-1)-b^2*(m+1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>2 && m<-1


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-2)/(d*(m+n-1)) + 
  1/(m+n-1)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n-3)*
    Simp[a*(a^2*(m+n-1)-b^2*(m+1))+b*(3*a^2-b^2)*(m+n-1)*Tan[c+d*x]+a*b^2*(2*m+3*n-4)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>2 && (RationalQ[m] && m>=-1 || IntegerQ[n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-2)/(d*(m+n-1)) + 
  1/(m+n-1)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n-3)*
    Simp[a*(a^2*(m+n-1)-b^2*(m+1))+b*(3*a^2-b^2)*(m+n-1)*Cot[c+d*x]+a*b^2*(2*m+3*n-4)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>2 && (RationalQ[m] && m>=-1 || IntegerQ[n])


Int[tan[c_.+d_.*x_]/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  b*x/(a^2+b^2) - a/(a^2+b^2)*Int[(b-a*Tan[c+d*x])/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  b*x/(a^2+b^2) - a/(a^2+b^2)*Int[(b-a*Cot[c+d*x])/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[tan[c_.+d_.*x_]]/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(b+a*Tan[c+d*x])/Sqrt[Tan[c+d*x]],x] - 
  a*b/(a^2+b^2)*Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*(a+b*Tan[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[cot[c_.+d_.*x_]]/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(b+a*Cot[c+d*x])/Sqrt[Cot[c+d*x]],x] - 
  a*b/(a^2+b^2)*Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*(a+b*Cot[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^(3/2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  -1/(a^2+b^2)*Int[(a-b*Tan[c+d*x])/Sqrt[Tan[c+d*x]],x] + 
  a^2/(a^2+b^2)*Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*(a+b*Tan[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]^(3/2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -1/(a^2+b^2)*Int[(a-b*Cot[c+d*x])/Sqrt[Cot[c+d*x]],x] + 
  a^2/(a^2+b^2)*Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*(a+b*Cot[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  Tan[c+d*x]^(m-2)/(b*d*(m-2)) - 
  1/b*Int[(Tan[c+d*x]^(m-3)*(a+b*Tan[c+d*x]+a*Tan[c+d*x]^2))/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>2 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -Cot[c+d*x]^(m-2)/(b*d*(m-2)) - 
  1/b*Int[(Cot[c+d*x]^(m-3)*(a+b*Cot[c+d*x]+a*Cot[c+d*x]^2))/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>2 && IntegerQ[2*m]


Int[1/(Sqrt[tan[c_.+d_.*x_]]*(a_+b_.*tan[c_.+d_.*x_])),x_Symbol] :=
  1/(a^2+b^2)*Int[(a-b*Tan[c+d*x])/Sqrt[Tan[c+d*x]],x] + 
  b^2/(a^2+b^2)*Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*(a+b*Tan[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[1/(Sqrt[cot[c_.+d_.*x_]]*(a_+b_.*cot[c_.+d_.*x_])),x_Symbol] :=
  1/(a^2+b^2)*Int[(a-b*Cot[c+d*x])/Sqrt[Cot[c+d*x]],x] + 
  b^2/(a^2+b^2)*Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*(a+b*Cot[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  Tan[c+d*x]^(m+1)/(a*d*(m+1)) - 
  1/a*Int[(Tan[c+d*x]^(m+1)*(b+a*Tan[c+d*x]+b*Tan[c+d*x]^2))/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -Cot[c+d*x]^(m+1)/(a*d*(m+1)) - 
  1/a*Int[Cot[c+d*x]^(m+1)*(b+a*Cot[c+d*x]+b*Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[tan[c_.+d_.*x_]^m_/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a/(a^2+b^2)*Int[Tan[c+d*x]^m,x] - 
  b/(a^2+b^2)*Int[Tan[c+d*x]^(m+1),x] + 
  b^2/(a^2+b^2)*Int[Tan[c+d*x]^m*(1+Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]]


Int[cot[c_.+d_.*x_]^m_/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  a/(a^2+b^2)*Int[Cot[c+d*x]^m,x] - 
  b/(a^2+b^2)*Int[Cot[c+d*x]^(m+1),x] + 
  b^2/(a^2+b^2)*Int[Cot[c+d*x]^m*(1+Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]]


Int[tan[c_.+d_.*x_]/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  1/2*Int[(I+Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] - 
  1/2*Int[(I-Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  1/2*Int[(I+Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] - 
  1/2*Int[(I-Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[tan[c_.+d_.*x_]]/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  1/2*Int[(I+Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] - 
  1/2*Int[(I-Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[cot[c_.+d_.*x_]]/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  1/2*Int[(I+Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] - 
  1/2*Int[(I-Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -Int[1/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] + 
  Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Int[1/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] + 
  Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  2*Tan[c+d*x]^(m-2)*Sqrt[a+b*Tan[c+d*x]]/(b*d*(2*m-3)) - 
  1/(b*(2*m-3))*Int[Tan[c+d*x]^(m-3)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[2*a*(m-2)+b*(2*m-3)*Tan[c+d*x]+2*a*(m-2)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>2 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -2*Cot[c+d*x]^(m-2)*Sqrt[a+b*Cot[c+d*x]]/(b*d*(2*m-3)) - 
  1/(b*(2*m-3))*Int[Cot[c+d*x]^(m-3)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[2*a*(m-2)+b*(2*m-3)*Cot[c+d*x]+2*a*(m-2)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>2 && IntegerQ[2*m]


Int[1/(tan[c_.+d_.*x_]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  -Int[Tan[c+d*x]/Sqrt[a+b*Tan[c+d*x]],x] + 
  Int[(1+Tan[c+d*x]^2)/(Tan[c+d*x]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[1/(cot[c_.+d_.*x_]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  -Int[Cot[c+d*x]/Sqrt[a+b*Cot[c+d*x]],x] + 
  Int[(1+Cot[c+d*x]^2)/(Cot[c+d*x]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[1/(Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  1/2*Int[(1-I*Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] + 
  1/2*Int[(1+I*Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[1/(Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  1/2*Int[(1-I*Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] + 
  1/2*Int[(1+I*Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  Tan[c+d*x]^(m+1)*Sqrt[a+b*Tan[c+d*x]]/(a*d*(m+1)) - 
  1/(2*a*(m+1))*Int[Tan[c+d*x]^(m+1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[3*b+2*b*m+2*a*(m+1)*Tan[c+d*x]+b*(2*m+3)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[cot[c_.+d_.*x_]^m_/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Cot[c+d*x]^(m+1)*Sqrt[a+b*Cot[c+d*x]]/(a*d*(m+1)) - 
  1/(2*a*(m+1))*Int[Cot[c+d*x]^(m+1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[3*b+2*b*m+2*a*(m+1)*Cot[c+d*x]+b*(2*m+3)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(a+b*Tan[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(b+a*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a+b*Cot[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[(b+a*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1


Int[Sqrt[tan[c_.+d_.*x_]]*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sqrt[Tan[c+d*x]]*(a+b*Tan[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) - 
  1/(2*(n+1)*(a^2+b^2))*
    Int[(b-2*a*(n+1)*Tan[c+d*x]+b*(2*n+3)*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^(n+1)/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[Sqrt[cot[c_.+d_.*x_]]*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Sqrt[Cot[c+d*x]]*(a+b*Cot[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) - 
  1/(2*(n+1)*(a^2+b^2))*
    Int[(b-2*a*(n+1)*Cot[c+d*x]+b*(2*n+3)*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^(n+1)/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[tan[c_.+d_.*x_]^(3/2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sqrt[Tan[c+d*x]]*(a+b*Tan[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) + 
  1/(2*(n+1)*(a^2+b^2))*
    Int[Simp[a+2*b*(n+1)*Tan[c+d*x]+a*(2*n+3)*Tan[c+d*x]^2,x]*(a+b*Tan[c+d*x])^(n+1)/Sqrt[Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[cot[c_.+d_.*x_]^(3/2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Sqrt[Cot[c+d*x]]*(a+b*Cot[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) + 
  1/(2*(n+1)*(a^2+b^2))*
    Int[Simp[a+2*b*(n+1)*Cot[c+d*x]+a*(2*n+3)*Cot[c+d*x]^2,x]*(a+b*Cot[c+d*x])^(n+1)/Sqrt[Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Tan[c+d*x]^(m-2)*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) - 
  1/(b*(n+1)*(a^2+b^2))*Int[Tan[c+d*x]^(m-3)*(a+b*Tan[c+d*x])^(n+1)*
     Simp[a^2*(m-2)+a*b*(n+1)*Tan[c+d*x]+(a^2*(m-2)-b^2*(n+1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>2 && IntegersQ[2*m,2*n]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Cot[c+d*x]^(m-2)*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) - 
  1/(b*(n+1)*(a^2+b^2))*Int[Cot[c+d*x]^(m-3)*(a+b*Cot[c+d*x])^(n+1)*
     Simp[a^2*(m-2)+a*b*(n+1)*Cot[c+d*x]+(a^2*(m-2)-b^2*(n+1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>2 && IntegersQ[2*m,2*n]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n+1)/(a*d*(n+1)*(a^2+b^2)) + 
  1/(a*(n+1)*(a^2+b^2))*
    Int[Tan[c+d*x]^m*Simp[a^2*(n+1)+b^2*(m+n+2)-a*b*(n+1)*Tan[c+d*x]+b^2*(m+n+2)*Tan[c+d*x]^2,x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && (RationalQ[m] && m<0 || IntegerQ[n])


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n+1)/(a*d*(n+1)*(a^2+b^2)) + 
  1/(a*(n+1)*(a^2+b^2))*
    Int[Cot[c+d*x]^m*Simp[a^2*(n+1)+b^2*(m+n+2)-a*b*(n+1)*Cot[c+d*x]+b^2*(m+n+2)*Cot[c+d*x]^2,x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && (RationalQ[m] && m<0 || IntegerQ[n])


Int[tan[c_.+d_.*x_]^m_.*(a_.+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2*Int[Tan[c+d*x]^m*(1-I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] + 
  1/2*Int[Tan[c+d*x]^m*(1+I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[cot[c_.+d_.*x_]^m_.*(a_.+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2*Int[Cot[c+d*x]^m*(1-I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] + 
  1/2*Int[Cot[c+d*x]^m*(1+I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[a^2+b^2] && Not[IntegerQ[n]]


Int[(e_*tan[c_.+d_.*x_])^m_*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m/Tan[c+d*x]^m*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_*cot[c_.+d_.*x_])^m_*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m/Cot[c+d*x]^m*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*Tan[c+d*x]^m*Int[(a+b*Tan[c+d*x])^n/Tan[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*tan[c_.+d_.*x_])^m_*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m*Cot[c+d*x]^m*Int[(a+b*Cot[c+d*x])^n/Cot[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_.*(f_.*tan[c_.+d_.*x_])^p_.*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*(f*Tan[c+d*x])^p/Tan[c+d*x]^(p-m)*Int[Tan[c+d*x]^(p-m)*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(e_.*tan[c_.+d_.*x_])^m_.*(f_.*cot[c_.+d_.*x_])^p_.*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m*(f*Cot[c+d*x])^p/Cot[c+d*x]^(p-m)*Int[Cot[c+d*x]^(p-m)*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


(* ::Subsection::Closed:: *)
(*7.2.2 tan(c+d x)^m (A+B tan(c+d x)) (a+b tan(c+d x))^n*)


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_])*(b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Tan[c+d*x])*(b*Tan[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,n},x] && IntegerQ[m]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_])*(b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Cot[c+d*x])*(b*Cot[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,n},x] && IntegerQ[m]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(b_*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]]*Int[Tan[c+d*x]^(m+n)*(A+B*Tan[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(b_*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]]*Int[Cot[c+d*x]^(m+n)*(A+B*Cot[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(b_*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Tan[c+d*x]]/Sqrt[b*Tan[c+d*x]]*Int[Tan[c+d*x]^(m+n)*(A+B*Tan[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(b_*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Cot[c+d*x]]/Sqrt[b*Cot[c+d*x]]*Int[Cot[c+d*x]^(m+n)*(A+B*Cot[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Tan[c+d*x])^n/Tan[c+d*x]^n*Int[Tan[c+d*x]^(m+n)*(A+B*Tan[c+d*x]),x] /;
FreeQ[{b,c,d,A,B,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cot[c+d*x])^n/Cot[c+d*x]^n*Int[Cot[c+d*x]^(m+n)*(A+B*Cot[c+d*x]),x] /;
FreeQ[{b,c,d,A,B,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[A*b-a*B]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[A*b-a*B]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])/tan[c_.+d_.*x_],x_Symbol] :=
  (A*b+a*B)*x + b*B*Int[Tan[c+d*x],x] + a*A*Int[1/Tan[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])/cot[c_.+d_.*x_],x_Symbol] :=
  (A*b+a*B)*x + b*B*Int[Cot[c+d*x],x] + a*A*Int[1/Cot[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a*A*Tan[c+d*x]^(m+1)/(d*(m+1)) + 
  Int[Tan[c+d*x]^(m+1)*Simp[A*b+a*B-(a*A-b*B)*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -a*A*Cot[c+d*x]^(m+1)/(d*(m+1)) + 
  Int[Cot[c+d*x]^(m+1)*Simp[A*b+a*B-(a*A-b*B)*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  b*B*Tan[c+d*x]^(m+1)/(d*(m+1)) + 
  Int[Tan[c+d*x]^m*Simp[a*A-b*B+(A*b+a*B)*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[m] && m<=-1]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -b*B*Cot[c+d*x]^(m+1)/(d*(m+1)) + 
  Int[Cot[c+d*x]^m*Simp[a*A-b*B+(A*b+a*B)*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[m] && m<=-1]


Int[tan[c_.+d_.*x_]*(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  B/b*Int[Tan[c+d*x],x] + (a*A+b*B)/a*Int[Tan[c+d*x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]*(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  B/b*Int[Cot[c+d*x],x] + (a*A+b*B)/a*Int[Cot[c+d*x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]*(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  A*x/b - a*A/b*Int[(1+Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[a*A+b*B]


Int[cot[c_.+d_.*x_]*(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  A*x/b - a*A/b*Int[(1+Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[a*A+b*B]


Int[tan[c_.+d_.*x_]*(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  (a*A+b*B)/(a^2+b^2)*Int[Tan[c+d*x],x] + 
  (A*b-a*B)/(a^2+b^2)*Int[Tan[c+d*x]*(b-a*Tan[c+d*x])/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[a*A+b*B]


Int[cot[c_.+d_.*x_]*(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  (a*A+b*B)/(a^2+b^2)*Int[Cot[c+d*x],x] + 
  (A*b-a*B)/(a^2+b^2)*Int[Cot[c+d*x]*(b-a*Cot[c+d*x])/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[a*A+b*B]


Int[tan[c_.+d_.*x_]*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Tan[c+d*x]*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Simp[A*b-a*B+(a*A*(n+1)-b*B*(n-1))*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && ZeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Cot[c+d*x]*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Simp[A*b-a*B+(a*A*(n+1)-b*B*(n-1))*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && ZeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(A*b-a*B)*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[Simp[A*b-a*B+(a*A+b*B)*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && NonzeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(A*b-a*B)*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[Simp[A*b-a*B+(a*A+b*B)*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<-1 && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  B*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) - 
  Int[(B-A*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[n] && n<=-1]


Int[cot[c_.+d_.*x_]*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) - 
  Int[(B-A*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[n] && n<=-1]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a*A*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-1)/(d*(m+1)) + 
  1/(m+1)*Int[Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-1)*
    Simp[A*b*(m-n+2)+a*B*(m+1)-(a*A*(m+n)-b*B*(m+1))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m<-1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*A*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-1)/(d*(m+1)) + 
  1/(m+1)*Int[Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-1)*
    Simp[A*b*(m-n+2)+a*B*(m+1)-(a*A*(m+n)-b*B*(m+1))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m<-1


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*B*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-1)/(d*(m+n)) + 
  1/(m+n)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n-1)*
    Simp[a*A*(m+n)-b*B*(m+1)+(a*B*(n-1)+(A*b+a*B)*(m+n))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*B*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-1)/(d*(m+n)) + 
  1/(m+n)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n-1)*
    Simp[a*A*(m+n)-b*B*(m+1)+(a*B*(n-1)+(A*b+a*B)*(m+n))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Tan[c+d*x]^m*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Tan[c+d*x]^(m-1)*(a+b*Tan[c+d*x])^(n+1)*
    Simp[m*(A*b-a*B)+(b*B*(m-n)+a*A*(m+n))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n<0 && m>0


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Cot[c+d*x]^m*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Cot[c+d*x]^(m-1)*(a+b*Cot[c+d*x])^(n+1)*
    Simp[m*(A*b-a*B)+(b*B*(m-n)+a*A*(m+n))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[m,n] && n<0 && m>0


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a*A+b*B)*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)*
    Simp[b*B*(m+1)+a*A*(m+2*n+1)-(A*b-a*B)*(m+n+1)*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0 && Not[RationalQ[m] && m>0]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (a*A+b*B)*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)*
    Simp[b*B*(m+1)+a*A*(m+2*n+1)-(A*b-a*B)*(m+n+1)*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0 && Not[RationalQ[m] && m>0]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  B*Tan[c+d*x]^m*(a+b*Tan[c+d*x])^n/(d*(m+n)) - 
  1/(a*(m+n))*Int[Tan[c+d*x]^(m-1)*Simp[B*a*m+(b*B*n-a*A*(m+n))*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*Cot[c+d*x]^m*(a+b*Cot[c+d*x])^n/(d*(m+n)) - 
  1/(a*(m+n))*Int[Cot[c+d*x]^(m-1)*Simp[B*a*m+(b*B*n-a*A*(m+n))*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+1)) - 
  1/(a*(m+1))*Int[Tan[c+d*x]^(m+1)*Simp[A*b*n-a*B*(m+1)+a*A*(m+n+1)*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+1)) - 
  1/(a*(m+1))*Int[Cot[c+d*x]^(m+1)*Simp[A*b*n-a*B*(m+1)+a*A*(m+n+1)*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[(A_+B_.*tan[c_.+d_.*x_])*Sqrt[a_+b_.*tan[c_.+d_.*x_]]/tan[c_.+d_.*x_],x_Symbol] :=
  -2*b*B/(Rt[a,2]*d)*ArcTanh[Sqrt[a+b*Tan[c+d*x]]/Rt[a,2]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && PosQ[a]


Int[(A_+B_.*cot[c_.+d_.*x_])*Sqrt[a_+b_.*cot[c_.+d_.*x_]]/cot[c_.+d_.*x_],x_Symbol] :=
  2*b*B/(Rt[a,2]*d)*ArcTanh[Sqrt[a+b*Cot[c+d*x]]/Rt[a,2]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && PosQ[a]


Int[(A_+B_.*tan[c_.+d_.*x_])*Sqrt[a_+b_.*tan[c_.+d_.*x_]]/tan[c_.+d_.*x_],x_Symbol] :=
  2*b*B/(Rt[-a,2]*d)*ArcTan[Sqrt[a+b*Tan[c+d*x]]/Rt[-a,2]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && NegQ[a]


Int[(A_+B_.*cot[c_.+d_.*x_])*Sqrt[a_+b_.*cot[c_.+d_.*x_]]/cot[c_.+d_.*x_],x_Symbol] :=
  -2*b*B/(Rt[-a,2]*d)*ArcTan[Sqrt[a+b*Cot[c+d*x]]/Rt[-a,2]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && NegQ[a]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_/tan[c_.+d_.*x_],x_Symbol] :=
  b*B/d*Subst[Int[(a+b*x)^(n-1)/x,x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && RationalQ[n] && 0<n<1


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_/cot[c_.+d_.*x_],x_Symbol] :=
  -b*B/d*Subst[Int[(a+b*x)^(n-1)/x,x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && RationalQ[n] && 0<n<1


Int[(A_+B_.*tan[c_.+d_.*x_])*Sqrt[a_+b_.*tan[c_.+d_.*x_]]/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[b,2]*B/d*ArcTanh[Rt[b,2]*Sqrt[Tan[c+d*x]]/Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && PosQ[b]


Int[(A_+B_.*cot[c_.+d_.*x_])*Sqrt[a_+b_.*cot[c_.+d_.*x_]]/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[b,2]*B/d*ArcTanh[Rt[b,2]*Sqrt[Cot[c+d*x]]/Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && PosQ[b]


Int[(A_+B_.*tan[c_.+d_.*x_])*Sqrt[a_+b_.*tan[c_.+d_.*x_]]/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[-b,2]*B/d*ArcTan[Rt[-b,2]*Sqrt[Tan[c+d*x]]/Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && NegQ[b]


Int[(A_+B_.*cot[c_.+d_.*x_])*Sqrt[a_+b_.*cot[c_.+d_.*x_]]/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[-b,2]*B/d*ArcTan[Rt[-b,2]*Sqrt[Cot[c+d*x]]/Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B] && NegQ[b]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  B*Tan[c+d*x]^m*(a+b*Tan[c+d*x])^n/(d*n*(-b*Tan[c+d*x]/a)^m)*Hypergeometric2F1[-m,n,n+1,(a+b*Tan[c+d*x])/a] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*Cot[c+d*x]^m*(a+b*Cot[c+d*x])^n/(d*n*(-b*Cot[c+d*x]/a)^m)*Hypergeometric2F1[-m,n,n+1,(a+b*Cot[c+d*x])/a] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && ZeroQ[A*b+a*B]


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_/tan[c_.+d_.*x_],x_Symbol] :=
  (A*b+a*B)/a*Int[(a+b*Tan[c+d*x])^n,x] + 
  A/a*Int[(a-b*Tan[c+d*x])*(a+b*Tan[c+d*x])^n/Tan[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_/cot[c_.+d_.*x_],x_Symbol] :=
  (A*b+a*B)/a*Int[(a+b*Cot[c+d*x])^n,x] + 
  A/a*Int[(a-b*Cot[c+d*x])*(a+b*Cot[c+d*x])^n/Cot[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b+a*B)/b*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^n,x] - 
  B/b*Int[Tan[c+d*x]^m*(a-b*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b+a*B)/b*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^n,x] - 
  B/b*Int[Cot[c+d*x]^m*(a-b*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2+b^2] && NonzeroQ[A*b+a*B]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+1)*((a+b*Tan[c+d*x])/a)^n)*
    AppellF1[m+1,1,-n,m+2,B*Tan[c+d*x]/A,-b*Tan[c+d*x]/a] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]] && 
  Not[IntegerQ[n]] && Not[IntegersQ[2*m,2*n]] && ZeroQ[A^2+B^2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+1)*((a+b*Cot[c+d*x])/a)^n)*
    AppellF1[m+1,1,-n,m+2,B*Cot[c+d*x]/A,-b*Cot[c+d*x]/a] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]] && 
  Not[IntegerQ[n]] && Not[IntegersQ[2*m,2*n]] && ZeroQ[A^2+B^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A+I*B)/2*Int[Tan[c+d*x]^m*(1-I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] + 
  (A-I*B)/2*Int[Tan[c+d*x]^m*(1+I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]] && 
  Not[IntegerQ[n]] && Not[IntegersQ[2*m,2*n]] && NonzeroQ[A^2+B^2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (A+I*B)/2*Int[Cot[c+d*x]^m*(1-I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] + 
  (A-I*B)/2*Int[Cot[c+d*x]^m*(1+I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && Not[IntegerQ[m]] && 
  Not[IntegerQ[n]] && Not[IntegersQ[2*m,2*n]] && NonzeroQ[A^2+B^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  2*B*Tan[c+d*x]^m*Sqrt[a+b*Tan[c+d*x]]/(d*(2*m+1)) - 
  1/(2*m+1)*Int[Tan[c+d*x]^(m-1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[2*a*B*m-(a*A-b*B)*(2*m+1)*Tan[c+d*x]-(a*B+A*b*(2*m+1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cot[c+d*x]^m*Sqrt[a+b*Cot[c+d*x]]/(d*(2*m+1)) - 
  1/(2*m+1)*Int[Cot[c+d*x]^(m-1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[2*a*B*m-(a*A-b*B)*(2*m+1)*Cot[c+d*x]-(a*B+A*b*(2*m+1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[(A_+B_.*tan[c_.+d_.*x_])*Sqrt[a_+b_.*tan[c_.+d_.*x_]]/tan[c_.+d_.*x_],x_Symbol] :=
  Int[(A*b+a*B-(a*A-b*B)*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] + 
  a*A*Int[(1+Tan[c+d*x]^2)/(Tan[c+d*x]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[(A_+B_.*cot[c_.+d_.*x_])*Sqrt[a_+b_.*cot[c_.+d_.*x_]]/cot[c_.+d_.*x_],x_Symbol] :=
  Int[(A*b+a*B-(a*A-b*B)*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] + 
  a*A*Int[(1+Cot[c+d*x]^2)/(Cot[c+d*x]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[(A_+B_.*tan[c_.+d_.*x_])*Sqrt[a_+b_.*tan[c_.+d_.*x_]]/Sqrt[tan[c_.+d_.*x_]],x_Symbol] :=
  Int[(a*A-b*B+(A*b+a*B)*Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] + 
  b*B*Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[(A_+B_.*cot[c_.+d_.*x_])*Sqrt[a_+b_.*cot[c_.+d_.*x_]]/Sqrt[cot[c_.+d_.*x_]],x_Symbol] :=
  Int[(a*A-b*B+(A*b+a*B)*Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] + 
  b*B*Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*Sqrt[a+b*Tan[c+d*x]]/(d*(m+1)) - 
  1/(2*(m+1))*Int[Tan[c+d*x]^(m+1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[A*b-2*a*B*(m+1)+2*(a*A-b*B)*(m+1)*Tan[c+d*x]+A*b*(2*m+3)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*Sqrt[a+b*Cot[c+d*x]]/(d*(m+1)) - 
  1/(2*(m+1))*Int[Cot[c+d*x]^(m+1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[A*b-2*a*B*(m+1)+2*(a*A-b*B)*(m+1)*Cot[c+d*x]+A*b*(2*m+3)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  a*A*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-1)/(d*(m+1)) + 
  1/(m+1)*Int[Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-2)*
    Simp[a*(a*B*(m+1)+A*b*(m-n+2))-(a^2*A-A*b^2-2*a*b*B)*(m+1)*Tan[c+d*x]+b*(b*B*(m+1)-a*A*(m+n))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*A*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-1)/(d*(m+1)) + 
  1/(m+1)*Int[Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-2)*
    Simp[a*(a*B*(m+1)+A*b*(m-n+2))-(a^2*A-A*b^2-2*a*b*B)*(m+1)*Cot[c+d*x]+b*(b*B*(m+1)-a*A*(m+n))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>1 && m<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b*B*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-1)/(d*(m+n)) + 
  1/(m+n)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n-2)*
    Simp[a*(a*A*(m+n)-b*B*(m+1))+(2*a*A*b+a^2*B-b^2*B)*(m+n)*Tan[c+d*x]+b*(A*b*(m+n)+a*B*(m+2*n-1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*B*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-1)/(d*(m+n)) + 
  1/(m+n)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n-2)*
    Simp[a*(a*A*(m+n)-b*B*(m+1))+(2*a*A*b+a^2*B-b^2*B)*(m+n)*Cot[c+d*x]+b*(A*b*(m+n)+a*B*(m+2*n-1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[Sqrt[tan[c_.+d_.*x_]]*(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(A*b-a*B+(a*A+b*B)*Tan[c+d*x])/Sqrt[Tan[c+d*x]],x] - 
  a*(A*b-a*B)/(a^2+b^2)*Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*(a+b*Tan[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[Sqrt[cot[c_.+d_.*x_]]*(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[(A*b-a*B+(a*A+b*B)*Cot[c+d*x])/Sqrt[Cot[c+d*x]],x] - 
  a*(A*b-a*B)/(a^2+b^2)*Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*(a+b*Cot[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  B*Tan[c+d*x]^(m-1)/(b*d*(m-1)) - 
  1/b*Int[Tan[c+d*x]^(m-2)*Simp[a*B+b*B*Tan[c+d*x]-(A*b-a*B)*Tan[c+d*x]^2,x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -B*Cot[c+d*x]^(m-1)/(b*d*(m-1)) - 
  1/b*Int[Cot[c+d*x]^(m-2)*Simp[a*B+b*B*Cot[c+d*x]-(A*b-a*B)*Cot[c+d*x]^2,x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>1


Int[(A_+B_.*tan[c_.+d_.*x_])/(tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Tan[c+d*x],x] - 
  (A*b-a*B)/a*Int[1/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[(A_+B_.*cot[c_.+d_.*x_])/(cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Cot[c+d*x],x] - 
  (A*b-a*B)/a*Int[1/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  A*Tan[c+d*x]^(m+1)/(a*d*(m+1)) - 
  1/a*Int[Tan[c+d*x]^(m+1)*Simp[A*b-a*B+a*A*Tan[c+d*x]+A*b*Tan[c+d*x]^2,x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)/(a*d*(m+1)) - 
  1/a*Int[Cot[c+d*x]^(m+1)*Simp[A*b-a*B+a*A*Cot[c+d*x]+A*b*Cot[c+d*x]^2,x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[Tan[c+d*x]^m*(a*A+b*B-(A*b-a*B)*Tan[c+d*x]),x] + 
  b*(A*b-a*B)/(a^2+b^2)*Int[Tan[c+d*x]^m*(1+Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[Cot[c+d*x]^m*(a*A+b*B-(A*b-a*B)*Cot[c+d*x]),x] + 
  b*(A*b-a*B)/(a^2+b^2)*Int[Cot[c+d*x]^m*(1+Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[Sqrt[tan[c_.+d_.*x_]]*(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  -Int[(B-A*Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] + 
  B*Int[(1+Tan[c+d*x]^2)/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2+b^2]


Int[Sqrt[cot[c_.+d_.*x_]]*(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -Int[(B-A*Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] + 
  B*Int[(1+Cot[c+d*x]^2)/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  2*B*Tan[c+d*x]^(m-1)*Sqrt[a+b*Tan[c+d*x]]/(b*d*(2*m-1)) - 
  1/(b*(2*m-1))*Int[Tan[c+d*x]^(m-2)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[2*a*B*(m-1)+b*B*(2*m-1)*Tan[c+d*x]+(2*a*B*(m-1)-A*b*(2*m-1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cot[c+d*x]^(m-1)*Sqrt[a+b*Cot[c+d*x]]/(b*d*(2*m-1)) - 
  1/(b*(2*m-1))*Int[Cot[c+d*x]^(m-2)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[2*a*B*(m-1)+b*B*(2*m-1)*Cot[c+d*x]+(2*a*B*(m-1)-A*b*(2*m-1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>1


Int[(A_+B_.*tan[c_.+d_.*x_])/(tan[c_.+d_.*x_]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  Int[(B-A*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] + 
  A*Int[(1+Tan[c+d*x]^2)/(Tan[c+d*x]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[(A_+B_.*cot[c_.+d_.*x_])/(cot[c_.+d_.*x_]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  Int[(B-A*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] + 
  A*Int[(1+Cot[c+d*x]^2)/(Cot[c+d*x]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2]


Int[(A_+B_.*tan[c_.+d_.*x_])/(Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  2*A/(d*Rt[(A*b+a*B)/A,2])*ArcTanh[Rt[(A*b+a*B)/A,2]*Sqrt[Tan[c+d*x]]/Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && PosQ[(A*b+a*B)/A]


Int[(A_+B_.*cot[c_.+d_.*x_])/(Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  -2*A/(d*Rt[(A*b+a*B)/A,2])*ArcTanh[Rt[(A*b+a*B)/A,2]*Sqrt[Cot[c+d*x]]/Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && PosQ[(A*b+a*B)/A]


Int[(A_+B_.*tan[c_.+d_.*x_])/(Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  2*A/(d*Rt[-(A*b+a*B)/A,2])*ArcTan[Rt[-(A*b+a*B)/A,2]*Sqrt[Tan[c+d*x]]/Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && NegQ[(A*b+a*B)/A]


Int[(A_+B_.*cot[c_.+d_.*x_])/(Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  -2*A/(d*Rt[-(A*b+a*B)/A,2])*ArcTan[Rt[-(A*b+a*B)/A,2]*Sqrt[Cot[c+d*x]]/Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2] && NegQ[(A*b+a*B)/A]


Int[(A_+B_.*tan[c_.+d_.*x_])/(Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  (A+I*B)/2*Int[(1-I*Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] + 
  (A-I*B)/2*Int[(1+I*Tan[c+d*x])/(Sqrt[Tan[c+d*x]]*Sqrt[a+b*Tan[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[A^2+B^2]


Int[(A_+B_.*cot[c_.+d_.*x_])/(Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  (A+I*B)/2*Int[(1-I*Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] + 
  (A-I*B)/2*Int[(1+I*Cot[c+d*x])/(Sqrt[Cot[c+d*x]]*Sqrt[a+b*Cot[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[A^2+B^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*Sqrt[a+b*Tan[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*Int[Tan[c+d*x]^(m+1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[2*a*B*(m+1)-A*b*(2*m+3)-2*a*A*(m+1)*Tan[c+d*x]-A*b*(2*m+3)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*Sqrt[a+b*Cot[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*Int[Cot[c+d*x]^(m+1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[2*a*B*(m+1)-A*b*(2*m+3)-2*a*A*(m+1)*Cot[c+d*x]-A*b*(2*m+3)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(A*b-a*B)*Tan[c+d*x]^(m-1)*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) + 
  1/(b*(n+1)*(a^2+b^2))*Int[Tan[c+d*x]^(m-2)*(a+b*Tan[c+d*x])^(n+1)*
    Simp[a*(A*b-a*B)*(m-1)+b*(A*b-a*B)*(n+1)*Tan[c+d*x]+(b^2*B*(n+1)-a^2*B*(m-1)+a*A*b*(m+n))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(A*b-a*B)*Cot[c+d*x]^(m-1)*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) + 
  1/(b*(n+1)*(a^2+b^2))*Int[Cot[c+d*x]^(m-2)*(a+b*Cot[c+d*x])^(n+1)*
    Simp[a*(A*b-a*B)*(m-1)+b*(A*b-a*B)*(n+1)*Cot[c+d*x]+(b^2*B*(n+1)-a^2*B*(m-1)+a*A*b*(m+n))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) - 
  1/((n+1)*(a^2+b^2))*Int[Tan[c+d*x]^(m-1)*(a+b*Tan[c+d*x])^(n+1)*
    Simp[m*(A*b-a*B)-(a*A+b*B)*(n+1)*Tan[c+d*x]+(A*b-a*B)*(m+n+1)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>0 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) - 
  1/((n+1)*(a^2+b^2))*Int[Cot[c+d*x]^(m-1)*(a+b*Cot[c+d*x])^(n+1)*
    Simp[m*(A*b-a*B)-(a*A+b*B)*(n+1)*Cot[c+d*x]+(A*b-a*B)*(m+n+1)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>0 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(A*b-a*B)*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n+1)/(a*d*(n+1)*(a^2+b^2)) + 
  1/(a*(n+1)*(a^2+b^2))*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)*
    Simp[A*(a^2*(n+1)+b^2*(m+n+2))-a*b*B*(m+1)+a*(a*B-b*A)*(n+1)*Tan[c+d*x]+(A*b^2-a*b*B)*(m+n+2)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(A*b-a*B)*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n+1)/(a*d*(n+1)*(a^2+b^2)) + 
  1/(a*(n+1)*(a^2+b^2))*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)*
    Simp[A*(a^2*(n+1)+b^2*(m+n+2))-a*b*B*(m+1)+a*(a*B-b*A)*(n+1)*Cot[c+d*x]+(A*b^2-a*b*B)*(m+n+2)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_/tan[c_.+d_.*x_],x_Symbol] :=
  -A*Hypergeometric2F1[1,n+1,n+2,(a+b*Tan[c+d*x])/a]*(a+b*Tan[c+d*x])^(n+1)/(a*d*(n+1)) + 
  A*B*Hypergeometric2F1[1,n+1,n+2,B*(a+b*Tan[c+d*x])/(A*b+a*B)]*(a+b*Tan[c+d*x])^(n+1)/(d*(A*b+a*B)*(n+1)) /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2]


Int[(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_/cot[c_.+d_.*x_],x_Symbol] :=
  A*Hypergeometric2F1[1,n+1,n+2,(a+b*Cot[c+d*x])/a]*(a+b*Cot[c+d*x])^(n+1)/(a*d*(n+1)) - 
  A*B*Hypergeometric2F1[1,n+1,n+2,B*(a+b*Cot[c+d*x])/(A*b+a*B)]*(a+b*Cot[c+d*x])^(n+1)/(d*(A*b+a*B)*(n+1)) /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  A^2/d*Subst[Int[x^m*(a+b*x)^n/(A-B*x),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -A^2/d*Subst[Int[x^m*(a+b*x)^n/(A-B*x),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && ZeroQ[A^2+B^2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A+I*B)/2*Int[Tan[c+d*x]^m*(1-I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] + 
  (A-I*B)/2*Int[Tan[c+d*x]^m*(1+I*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[A^2+B^2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (A+I*B)/2*Int[Cot[c+d*x]^m*(1-I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] + 
  (A-I*B)/2*Int[Cot[c+d*x]^m*(1+I*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2+b^2] && NonzeroQ[A^2+B^2]


Int[(e_*tan[c_.+d_.*x_])^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m/Tan[c+d*x]^m*Int[Tan[c+d*x]^m*(A+B*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_*cot[c_.+d_.*x_])^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m/Cot[c+d*x]^m*Int[Cot[c+d*x]^m*(A+B*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_*(A_+B_.*tan[c_.+d_.*x_])*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*Tan[c+d*x]^m*Int[(A+B*Tan[c+d*x])*(a+b*Tan[c+d*x])^n/Tan[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*tan[c_.+d_.*x_])^m_*(A_+B_.*cot[c_.+d_.*x_])*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m*Cot[c+d*x]^m*Int[(A+B*Cot[c+d*x])*(a+b*Cot[c+d*x])^n/Cot[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_.*(f_.*tan[c_.+d_.*x_])^p_.*(A_.+B_.*tan[c_.+d_.*x_])*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*(f*Tan[c+d*x])^p/Tan[c+d*x]^(p-m)*Int[Tan[c+d*x]^(p-m)*(A+B*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x]


Int[(e_.*tan[c_.+d_.*x_])^m_.*(f_.*cot[c_.+d_.*x_])^p_.*(A_.+B_.*cot[c_.+d_.*x_])*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m*(f*Cot[c+d*x])^p/Cot[c+d*x]^(p-m)*Int[Cot[c+d*x]^(p-m)*(A+B*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x]


Int[u_.*(A_+B_.*cot[c_.+d_.*x_])*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Tan[c+d*x])*(a+b*Tan[c+d*x])^n/Tan[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B,n},x]


Int[u_.*(A_+B_.*tan[c_.+d_.*x_])*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Cot[c+d*x])*(a+b*Cot[c+d*x])^n/Cot[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B,n},x]


(* ::Subsection::Closed:: *)
(*7.2.3 tan(c+d x)^m (A+B tan(c+d x)+C tan(c+d x)^2) (a+b tan(c+d x))^n*)


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(a_.+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  A*Log[RemoveContent[a+b*Tan[c+d*x],x]]/(b*d) /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(a_.+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -A*Log[RemoveContent[a+b*Cot[c+d*x],x]]/(b*d) /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[A-C] && NonzeroQ[n+1]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -A*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[A-C] && NonzeroQ[n+1]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[(A+C*Tan[c+d*x]^2)/Tan[c+d*x],x] - b/a*Int[(A+C*Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[(A+C*Cot[c+d*x]^2)/Tan[c+d*x],x] - b/a*Int[(A+C*Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(tan[c_.+d_.*x_]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  -2*A/(Rt[a,2]*d)*ArcTanh[Sqrt[a + b*Tan[c + d*x]]/Rt[a,2]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && PosQ[a]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(cot[c_.+d_.*x_]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  2*A/(Rt[a,2]*d)*ArcTanh[Sqrt[a + b*Cot[c + d*x]]/Rt[a,2]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && PosQ[a]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(tan[c_.+d_.*x_]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  2*A/(Rt[-a,2]*d)*ArcTan[Sqrt[a + b*Tan[c + d*x]]/Rt[-a,2]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && NegQ[a]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(cot[c_.+d_.*x_]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  -2*A/(Rt[-a,2]*d)*ArcTan[Sqrt[a + b*Cot[c + d*x]]/Rt[-a,2]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && NegQ[a]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(Sqrt[tan[c_.+d_.*x_]]*(a_+b_.*tan[c_.+d_.*x_])),x_Symbol] :=
  2*A/(b*d)*Rt[b/a,2]*ArcTan[Rt[b/a,2]*Sqrt[Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && PosQ[b/a]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(Sqrt[cot[c_.+d_.*x_]]*(a_+b_.*cot[c_.+d_.*x_])),x_Symbol] :=
  -2*A/(b*d)*Rt[b/a,2]*ArcTan[Rt[b/a,2]*Sqrt[Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && PosQ[b/a]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(Sqrt[tan[c_.+d_.*x_]]*(a_+b_.*tan[c_.+d_.*x_])),x_Symbol] :=
  -2*A/(b*d)*Rt[-b/a,2]*ArcTanh[Rt[-b/a,2]*Sqrt[Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && NegQ[b/a]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(Sqrt[cot[c_.+d_.*x_]]*(a_+b_.*cot[c_.+d_.*x_])),x_Symbol] :=
  2*A/(b*d)*Rt[-b/a,2]*ArcTanh[Rt[-b/a,2]*Sqrt[Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && NegQ[b/a]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  2*A/(d*Rt[b,2])*ArcTanh[Rt[b,2]*Sqrt[Tan[c+d*x]]/Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && PosQ[b]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  -2*A/(d*Rt[b,2])*ArcTanh[Rt[b,2]*Sqrt[Cot[c+d*x]]/Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && PosQ[b]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(Sqrt[tan[c_.+d_.*x_]]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  2*A/(d*Rt[-b,2])*ArcTan[Rt[-b,2]*Sqrt[Tan[c+d*x]]/Sqrt[a+b*Tan[c+d*x]]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && NegQ[b]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(Sqrt[cot[c_.+d_.*x_]]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  -2*A/(d*Rt[-b,2])*ArcTan[Rt[-b,2]*Sqrt[Cot[c+d*x]]/Sqrt[a+b*Cot[c+d*x]]] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[A-C] && NegQ[b]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  A/d*Subst[Int[x^m*(a+b*x)^n,x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[A-C] && RationalQ[m]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -A/d*Subst[Int[x^m*(a+b*x)^n,x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[A-C] && RationalQ[m]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  A*Tan[c+d*x]^(m+1)/(a*d*(m+1))*Hypergeometric2F1[1,m+1,m+2,-b*Tan[c+d*x]/a] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[A-C] && NonzeroQ[m+1]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)/(a*d*(m+1))*Hypergeometric2F1[1,m+1,m+2,-b*Cot[c+d*x]/a] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[A-C] && NonzeroQ[m+1]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(-b*Tan[c+d*x]/a)^m)*
    Hypergeometric2F1[-m,n+1,n+2,(a+b*Tan[c+d*x])/a] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[A-C] && NonzeroQ[n+1]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -A*Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(-b*Cot[c+d*x]/a)^m)*
    Hypergeometric2F1[-m,n+1,n+2,(a+b*Cot[c+d*x])/a] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[A-C] && NonzeroQ[n+1]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/tan[c_.+d_.*x_],x_Symbol] :=
  A*Int[Cot[c+d*x],x] + C*Int[Tan[c+d*x],x] /;
FreeQ[{c,d,A,C},x] && NonzeroQ[A-C]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Tan[c+d*x],x] + C*Int[Cot[c+d*x],x] /;
FreeQ[{c,d,A,C},x] && NonzeroQ[A-C]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)*(b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*(b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) - 
  (A-C)/b^2*Int[(b*Tan[c+d*x])^(n+2),x] /;
FreeQ[{b,c,d,A,C},x] && NonzeroQ[A-C] && RationalQ[n] && n<-1


Int[(A_+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*(b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) - 
  (A-C)/b^2*Int[(b*Cot[c+d*x])^(n+2),x] /;
FreeQ[{b,c,d,A,C},x] && NonzeroQ[A-C] && RationalQ[n] && n<-1


Int[(A_+C_.*tan[c_.+d_.*x_]^2)*(b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*(b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) + 
  (A-C)*Int[(b*Tan[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,C,n},x] && NonzeroQ[A-C] && Not[RationalQ[n] && n<=-1]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*(b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) + 
  (A-C)*Int[(b*Cot[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,C,n},x] && NonzeroQ[A-C] && Not[RationalQ[n] && n<=-1]


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(b*Tan[c+d*x])^(n+1),x] + 
  Int[(A+C*Tan[c+d*x]^2)*(b*Tan[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,B,C},x] && IntegerQ[n]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(b*Cot[c+d*x])^(n+1),x] + 
  Int[(A+C*Cot[c+d*x]^2)*(b*Cot[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,B,C},x] && IntegerQ[n]


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Int[(1+Tan[c+d*x]^2)*(b*Tan[c+d*x])^n,x] + Int[(A-C+B*Tan[c+d*x])*(b*Tan[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,B,C,n},x] && Not[IntegerQ[n]]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Int[(1+Cot[c+d*x]^2)*(b*Cot[c+d*x])^n,x] + Int[(A-C+B*Cot[c+d*x])*(b*Cot[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,B,C,n},x] && Not[IntegerQ[n]]


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[Simp[b*B-a*C+b*C*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[Simp[b*B-a*C+b*C*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -C/b^2*Int[(a-b*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[A*b^2+a^2*C]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -C/b^2*Int[(a-b*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[A*b^2+a^2*C]


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a*A+b*B-a*C)*Tan[c+d*x]*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[(a+b*Tan[c+d*x])^(n+1)*
    Simp[(b*B-a*C)+a*A*(2*n+1)+(b*C*(-n+1)-(A*b-a*B)*(n+1))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[n] && n<=-1 && ZeroQ[a^2+b^2]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (a*A+b*B-a*C)*Cot[c+d*x]*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[(a+b*Cot[c+d*x])^(n+1)*
    Simp[(b*B-a*C)+a*A*(2*n+1)+(b*C*(-n+1)-(A*b-a*B)*(n+1))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[n] && n<=-1 && ZeroQ[a^2+b^2]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(A-C)*Tan[c+d*x]*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[(a+b*Tan[c+d*x])^(n+1)*
    Simp[-a*C+a*A*(2*n+1)+(b*C*(-n+1)-A*b*(n+1))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[n] && n<=-1 && ZeroQ[a^2+b^2]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(A-C)*Cot[c+d*x]*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[(a+b*Cot[c+d*x])^(n+1)*
    Simp[-a*C+a*A*(2*n+1)+(b*C*(-n+1)-A*b*(n+1))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[n] && n<=-1 && ZeroQ[a^2+b^2]


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  (a*A+b*B-a*C)*x/(a^2+b^2) + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(1+Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && ZeroQ[A*b-a*B-b*C]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  (a*A+b*B-a*C)*x/(a^2+b^2) + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(1+Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && ZeroQ[A*b-a*B-b*C]


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  (a*A+b*B-a*C)*x/(a^2+b^2) - 
  (A*b-a*B-b*C)/(a^2+b^2)*Int[Tan[c+d*x],x] + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(1+Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && NonzeroQ[a^2+b^2] && NonzeroQ[A*b-a*B-b*C]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  (a*A+b*B-a*C)*x/(a^2+b^2) - 
  (A*b-a*B-b*C)/(a^2+b^2)*Int[Cot[c+d*x],x] + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[(1+Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && NonzeroQ[a^2+b^2] && NonzeroQ[A*b-a*B-b*C]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a*(A-C)*x/(a^2+b^2) - 
  b*(A-C)/(a^2+b^2)*Int[Tan[c+d*x],x] + 
  (a^2*C+A*b^2)/(a^2+b^2)*Int[(1+Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2*C+A*b^2] && NonzeroQ[a^2+b^2] && NonzeroQ[A-C]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  a*(A-C)*x/(a^2+b^2) - 
  b*(A-C)/(a^2+b^2)*Int[Cot[c+d*x],x] + 
  (a^2*C+A*b^2)/(a^2+b^2)*Int[(1+Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2*C+A*b^2] && NonzeroQ[a^2+b^2] && NonzeroQ[A-C]


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[Simp[b*B+a*(A-C)-(A*b-a*B-b*C)*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[n] && n<-1 && NonzeroQ[a^2+b^2]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[Simp[b*B+a*(A-C)-(A*b-a*B-b*C)*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && RationalQ[n] && n<-1 && NonzeroQ[a^2+b^2]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[Simp[a*(A-C)-(A*b-b*C)*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[n] && n<-1 && NonzeroQ[a^2+b^2]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) + 
  1/(a^2+b^2)*Int[Simp[a*(A-C)-(A*b-b*C)*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[A*b^2+a^2*C] && RationalQ[n] && n<-1 && NonzeroQ[a^2+b^2]


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) + Int[(A-C+B*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && Not[RationalQ[n] && n<=-1]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) + Int[(A-C+B*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[A*b^2-a*b*B+a^2*C] && Not[RationalQ[n] && n<=-1]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) + (A-C)*Int[(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[A*b^2+a^2*C] && Not[RationalQ[n] && n<=-1]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) + (A-C)*Int[(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[A*b^2+a^2*C] && Not[RationalQ[n] && n<=-1]


Int[tan[c_.+d_.*x_]^m_.*(B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[Tan[c+d*x]^(m+1)*(B+C*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,m,n},x]


Int[cot[c_.+d_.*x_]^m_.*(B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[Cot[c+d*x]^(m+1)*(B+C*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,m,n},x]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2)*(b*Tan[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,C,n},x] && IntegerQ[m]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2)*(b*Cot[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,C,n},x] && IntegerQ[m]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+C*Tan[c+d*x]^2)*(b*Tan[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,C,n},x] && IntegerQ[m]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+C*Cot[c+d*x]^2)*(b*Cot[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,C,n},x] && IntegerQ[m]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(b_*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]]*Int[Tan[c+d*x]^(m+n)*(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(b_*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]]*Int[Cot[c+d*x]^(m+n)*(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[tan[c_.+d_.*x_]^m_*(A_+C_.*tan[c_.+d_.*x_]^2)*(b_*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Tan[c+d*x]]/Sqrt[Tan[c+d*x]]*Int[Tan[c+d*x]^(m+n)*(A+C*Tan[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[cot[c_.+d_.*x_]^m_*(A_+C_.*cot[c_.+d_.*x_]^2)*(b_*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Cot[c+d*x]]/Sqrt[Cot[c+d*x]]*Int[Cot[c+d*x]^(m+n)*(A+C*Cot[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(b_*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Tan[c+d*x]]/Sqrt[b*Tan[c+d*x]]*Int[Tan[c+d*x]^(m+n)*(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(b_*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Cot[c+d*x]]/Sqrt[b*Cot[c+d*x]]*Int[Cot[c+d*x]^(m+n)*(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[tan[c_.+d_.*x_]^m_*(A_+C_.*tan[c_.+d_.*x_]^2)*(b_*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Tan[c+d*x]]/Sqrt[b*Tan[c+d*x]]*Int[Tan[c+d*x]^(m+n)*(A+C*Tan[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[cot[c_.+d_.*x_]^m_*(A_+C_.*cot[c_.+d_.*x_]^2)*(b_*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Cot[c+d*x]]/Sqrt[b*Cot[c+d*x]]*Int[Cot[c+d*x]^(m+n)*(A+C*Cot[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Tan[c+d*x])^n/Tan[c+d*x]^n*Int[Tan[c+d*x]^(m+n)*(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cot[c+d*x])^n/Cot[c+d*x]^n*Int[Cot[c+d*x]^(m+n)*(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Tan[c+d*x])^n/Tan[c+d*x]^n*Int[Tan[c+d*x]^(m+n)*(A+C*Tan[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C,m,n},x]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cot[c+d*x])^n/Cot[c+d*x]^n*Int[Cot[c+d*x]^(m+n)*(A+C*Cot[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C,m,n},x]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[Tan[c+d*x]^m*Simp[b*B-a*C+b*C*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[Cot[c+d*x]^m*Simp[b*B-a*C+b*C*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  C/b^2*Int[Tan[c+d*x]^m*Simp[-a+b*Tan[c+d*x],x]*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[A*b^2+a^2*C]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  C/b^2*Int[Cot[c+d*x]^m*Simp[-a+b*Cot[c+d*x],x]*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[A*b^2+a^2*C]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a*A*Tan[c+d*x]^(m+1)/(d*(m+1)) + 
  Int[Tan[c+d*x]^(m+1)*Simp[b*A+a*B-(a*A-b*B-a*C)*Tan[c+d*x]+b*C*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -a*A*Cot[c+d*x]^(m+1)/(d*(m+1)) + 
  Int[Cot[c+d*x]^(m+1)*Simp[b*A+a*B-(a*A-b*B-a*C)*Cot[c+d*x]+b*C*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  a*A*Tan[c+d*x]^(m+1)/(d*(m+1)) + 
  Int[Tan[c+d*x]^(m+1)*Simp[b*A-(a*A-a*C)*Tan[c+d*x]+b*C*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -a*A*Cot[c+d*x]^(m+1)/(d*(m+1)) + 
  Int[Cot[c+d*x]^(m+1)*Simp[b*A-(a*A-a*C)*Cot[c+d*x]+b*C*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  b*C*Tan[c+d*x]^(m+2)/(d*(m+2)) + 
  Int[Tan[c+d*x]^m*Simp[a*A+(A*b+a*B-b*C)*Tan[c+d*x]+(b*B+a*C)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && Not[RationalQ[m] && m<-1]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -b*C*Cot[c+d*x]^(m+2)/(d*(m+2)) + 
  Int[Cot[c+d*x]^m*Simp[a*A+(A*b+a*B-b*C)*Cot[c+d*x]+(b*B+a*C)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && Not[RationalQ[m] && m<-1]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  b*C*Tan[c+d*x]^(m+2)/(d*(m+2)) + 
  Int[Tan[c+d*x]^m*Simp[a*A+(A*b-b*C)*Tan[c+d*x]+a*C*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && Not[RationalQ[m] && m<-1]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -b*C*Cot[c+d*x]^(m+2)/(d*(m+2)) + 
  Int[Cot[c+d*x]^m*Simp[a*A+(A*b-b*C)*Cot[c+d*x]+a*C*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && Not[RationalQ[m] && m<-1]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a*A+b*B-a*C)*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)*
    Simp[(b*B-a*C)*(m+1)+a*A*(m+2*n+1)+(b*C*(m-n+1)-(A*b-a*B)*(m+n+1))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (a*A+b*B-a*C)*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)*
    Simp[(b*B-a*C)*(m+1)+a*A*(m+2*n+1)+(b*C*(m-n+1)-(A*b-a*B)*(m+n+1))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(A-C)*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)*
    Simp[-a*C*(m+1)+a*A*(m+2*n+1)+(b*C*(m-n+1)-A*b*(m+n+1))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(A-C)*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(2*a*d*n) + 
  1/(2*a^2*n)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)*
    Simp[-a*C*(m+1)+a*A*(m+2*n+1)+(b*C*(m-n+1)-A*b*(m+n+1))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+1)) - 
  1/(a*(m+1))*Int[Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n*
    Simp[A*b*n-a*B*(m+1)+a*(A*(m+n+1)-C*(m+1))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+1)) - 
  1/(a*(m+1))*Int[Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n*
    Simp[A*b*n-a*B*(m+1)+a*(A*(m+n+1)-C*(m+1))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+1)) - 
  1/(a*(m+1))*Int[Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n*
    Simp[A*b*n+a*(A*(m+n+1)-C*(m+1))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+1)) - 
  1/(a*(m+1))*Int[Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n*
    Simp[A*b*n+a*(A*(m+n+1)-C*(m+1))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+n+1)) - 
  1/(a*(m+n+1))*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^n*
    Simp[a*C*(m+1)-a*A*(m+n+1)+(b*C*n-a*B*(m+n+1))*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && ZeroQ[a^2+b^2] && NonzeroQ[m+n+1]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+n+1)) - 
  1/(a*(m+n+1))*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^n*
    Simp[a*C*(m+1)-a*A*(m+n+1)+(b*C*n-a*B*(m+n+1))*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && ZeroQ[a^2+b^2] && NonzeroQ[m+n+1]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+n+1)) - 
  1/(a*(m+n+1))*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^n*
    Simp[a*C*(m+1)-a*A*(m+n+1)+b*C*n*Tan[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[a^2+b^2] && NonzeroQ[m+n+1]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+n+1)) - 
  1/(a*(m+n+1))*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^n*
    Simp[a*C*(m+1)-a*A*(m+n+1)+b*C*n*Cot[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[a^2+b^2] && NonzeroQ[m+n+1]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+1)) + 
  1/(m+1)*Int[Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-1)*
    Simp[a*B*(m+1)-A*b*n+(b*B-a*(A-C))*(m+1)*Tan[c+d*x]+b*(C*(m+1)-A*(m+n+1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>0 && m<-1


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+1)) + 
  1/(m+1)*Int[Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-1)*
    Simp[a*B*(m+1)-A*b*n+(b*B-a*(A-C))*(m+1)*Cot[c+d*x]+b*(C*(m+1)-A*(m+n+1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>0 && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+1)) - 
  1/(m+1)*Int[Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n-1)*
    Simp[A*b*n+a*(A-C)*(m+1)*Tan[c+d*x]-b*(C*(m+1)-A*(m+n+1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>0 && m<-1


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+1)) - 
  1/(m+1)*Int[Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n-1)*
    Simp[A*b*n+a*(A-C)*(m+1)*Cot[c+d*x]-b*(C*(m+1)-A*(m+n+1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n>0 && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+n+1)) + 
  1/(m+n+1)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n-1)*
    Simp[(A*a*(m+n+1)-C*(m+1)*a)+(a*B+b*(A-C))*(m+n+1)*Tan[c+d*x]+(a*C*n+b*B*(m+n+1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+n+1)) + 
  1/(m+n+1)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n-1)*
    Simp[(A*a*(m+n+1)-C*(m+1)*a)+(a*B+b*(A-C))*(m+n+1)*Cot[c+d*x]+(a*C*n+b*B*(m+n+1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^n/(d*(m+n+1)) + 
  1/(m+n+1)*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n-1)*
    Simp[(A*a*(m+n+1)-C*(m+1)*a)+b*(A-C)*(m+n+1)*Tan[c+d*x]+a*C*n*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^n/(d*(m+n+1)) + 
  1/(m+n+1)*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n-1)*
    Simp[(A*a*(m+n+1)-C*(m+1)*a)+b*(A-C)*(m+n+1)*Cot[c+d*x]+a*C*n*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  C*Tan[c+d*x]^m/(b*d*m) - 
  1/b*Int[Tan[c+d*x]^(m-1)*Simp[a*C-b*(A-C)*Tan[c+d*x]+(a*C-b*B)*Tan[c+d*x]^2,x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -C*Cot[c+d*x]^m/(b*d*m) - 
  1/b*Int[Cot[c+d*x]^(m-1)*Simp[a*C-b*(A-C)*Cot[c+d*x]+(a*C-b*B)*Cot[c+d*x]^2,x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  C*Tan[c+d*x]^m/(b*d*m) - 
  1/b*Int[Tan[c+d*x]^(m-1)*Simp[a*C-b*(A-C)*Tan[c+d*x]+a*C*Tan[c+d*x]^2,x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -C*Cot[c+d*x]^m/(b*d*m) - 
  1/b*Int[Cot[c+d*x]^(m-1)*Simp[a*C-b*(A-C)*Cot[c+d*x]+a*C*Cot[c+d*x]^2,x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/(tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Tan[c+d*x],x] - 
  1/a*Int[Simp[b*A-a*B-a*C*Tan[c+d*x],x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/(cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Cot[c+d*x],x] - 
  1/a*Int[Simp[b*A-a*B-a*C*Cot[c+d*x],x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(tan[c_.+d_.*x_]*(a_+b_.*tan[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Tan[c+d*x],x] - 
  1/a*Int[Simp[b*A-a*C*Tan[c+d*x],x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(cot[c_.+d_.*x_]*(a_+b_.*cot[c_.+d_.*x_])),x_Symbol] :=
  A/a*Int[1/Cot[c+d*x],x] - 
  1/a*Int[Simp[b*A-a*C*Cot[c+d*x],x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  A*Tan[c+d*x]^(m+1)/(a*d*(m+1)) + 
  1/a*Int[Tan[c+d*x]^(m+1)*Simp[a*B-A*b-a*(A-C)*Tan[c+d*x]-A*b*Tan[c+d*x]^2,x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)/(a*d*(m+1)) + 
  1/a*Int[Cot[c+d*x]^(m+1)*Simp[a*B-A*b-a*(A-C)*Cot[c+d*x]-A*b*Cot[c+d*x]^2,x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  A*Tan[c+d*x]^(m+1)/(a*d*(m+1)) - 
  1/a*Int[Tan[c+d*x]^(m+1)*Simp[A*b+a*(A-C)*Tan[c+d*x]+A*b*Tan[c+d*x]^2,x]/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)/(a*d*(m+1)) - 
  1/a*Int[Cot[c+d*x]^(m+1)*Simp[A*b+a*(A-C)*Cot[c+d*x]+A*b*Cot[c+d*x]^2,x]/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[Tan[c+d*x]^m*(b*B+a*(A-C)-(A*b-a*B-b*C)*Tan[c+d*x]),x] + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[Tan[c+d*x]^m*(1+Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)]


Int[cot[c_.+d_.*x_]^m_*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2+b^2)*Int[Cot[c+d*x]^m*(b*B+a*(A-C)-(A*b-a*B-b*C)*Cot[c+d*x]),x] + 
  (A*b^2-a*b*B+a^2*C)/(a^2+b^2)*Int[Cot[c+d*x]^m*(1+Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)]


Int[tan[c_.+d_.*x_]^m_*(A_+C_.*tan[c_.+d_.*x_]^2)/(a_+b_.*tan[c_.+d_.*x_]),x_Symbol] :=
  (A-C)/(a^2+b^2)*Int[Tan[c+d*x]^m*(a-b*Tan[c+d*x]),x] + 
  (A*b^2+a^2*C)/(a^2+b^2)*Int[Tan[c+d*x]^m*(1+Tan[c+d*x]^2)/(a+b*Tan[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)] && NonzeroQ[A-C]


Int[cot[c_.+d_.*x_]^m_*(A_+C_.*cot[c_.+d_.*x_]^2)/(a_+b_.*cot[c_.+d_.*x_]),x_Symbol] :=
  (A-C)/(a^2+b^2)*Int[Cot[c+d*x]^m*(a-b*Cot[c+d*x]),x] + 
  (A*b^2+a^2*C)/(a^2+b^2)*Int[Cot[c+d*x]^m*(1+Cot[c+d*x]^2)/(a+b*Cot[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)] && NonzeroQ[A-C]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  2*C*Tan[c+d*x]^m*Sqrt[a+b*Tan[c+d*x]]/(b*d*(2*m+1)) - 
  1/(b*(2*m+1))*Int[Tan[c+d*x]^(m-1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[2*a*C*m-b*(A-C)*(2*m+1)*Tan[c+d*x]+(2*a*C*m-b*B*(2*m+1))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -2*C*Cot[c+d*x]^m*Sqrt[a+b*Cot[c+d*x]]/(b*d*(2*m+1)) - 
  1/(b*(2*m+1))*Int[Cot[c+d*x]^(m-1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[2*a*C*m-b*(A-C)*(2*m+1)*Cot[c+d*x]+(2*a*C*m-b*B*(2*m+1))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  2*C*Tan[c+d*x]^m*Sqrt[a+b*Tan[c+d*x]]/(b*d*(2*m+1)) - 
  1/(b*(2*m+1))*Int[Tan[c+d*x]^(m-1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[2*a*C*m-b*(A-C)*(2*m+1)*Tan[c+d*x]+2*a*C*m*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -2*C*Cot[c+d*x]^m*Sqrt[a+b*Cot[c+d*x]]/(b*d*(2*m+1)) - 
  1/(b*(2*m+1))*Int[Cot[c+d*x]^(m-1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[2*a*C*m-b*(A-C)*(2*m+1)*Cot[c+d*x]+2*a*C*m*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0


Int[(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/(tan[c_.+d_.*x_]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  A*Int[(1+Tan[c+d*x]^2)/(Tan[c+d*x]*Sqrt[a+b*Tan[c+d*x]]),x] + 
  Int[Simp[B-(A-C)*Tan[c+d*x],x]/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2]


Int[(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/(cot[c_.+d_.*x_]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  A*Int[(1+Cot[c+d*x]^2)/(Cot[c+d*x]*Sqrt[a+b*Cot[c+d*x]]),x] + 
  Int[Simp[B-(A-C)*Cot[c+d*x],x]/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2]


Int[(A_+C_.*tan[c_.+d_.*x_]^2)/(tan[c_.+d_.*x_]*Sqrt[a_+b_.*tan[c_.+d_.*x_]]),x_Symbol] :=
  A*Int[(1+Tan[c+d*x]^2)/(Tan[c+d*x]*Sqrt[a+b*Tan[c+d*x]]),x] - 
  (A-C)*Int[Tan[c+d*x]/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2]


Int[(A_+C_.*cot[c_.+d_.*x_]^2)/(cot[c_.+d_.*x_]*Sqrt[a_+b_.*cot[c_.+d_.*x_]]),x_Symbol] :=
  A*Int[(1+Cot[c+d*x]^2)/(Cot[c+d*x]*Sqrt[a+b*Cot[c+d*x]]),x] - 
  (A-C)*Int[Cot[c+d*x]/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*Sqrt[a+b*Tan[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*Int[Tan[c+d*x]^(m+1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[2*a*B*(m+1)-A*b*(2*m+3)-2*a*(A-C)*(m+1)*Tan[c+d*x]-A*b*(2*m+3)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*Sqrt[a+b*Cot[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*Int[Cot[c+d*x]^(m+1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[2*a*B*(m+1)-A*b*(2*m+3)-2*a*(A-C)*(m+1)*Cot[c+d*x]-A*b*(2*m+3)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  A*Tan[c+d*x]^(m+1)*Sqrt[a+b*Tan[c+d*x]]/(a*d*(m+1)) - 
  1/(2*a*(m+1))*Int[Tan[c+d*x]^(m+1)/Sqrt[a+b*Tan[c+d*x]]*
    Simp[A*b*(2*m+3)+2*a*(A-C)*(m+1)*Tan[c+d*x]+A*b*(2*m+3)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  -A*Cot[c+d*x]^(m+1)*Sqrt[a+b*Cot[c+d*x]]/(a*d*(m+1)) + 
  1/(2*a*(m+1))*Int[Cot[c+d*x]^(m+1)/Sqrt[a+b*Cot[c+d*x]]*
    Simp[A*b*(2*m+3)+2*a*(A-C)*(m+1)*Cot[c+d*x]+A*b*(2*m+3)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m<-1


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  Int[Tan[c+d*x]^m*(A-C+B*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x] + 
  C*Int[Tan[c+d*x]^m*(1+Tan[c+d*x]^2)/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  Int[Cot[c+d*x]^m*(A-C+B*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x] + 
  C*Int[Cot[c+d*x]^m*(1+Cot[c+d*x]^2)/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)/Sqrt[a_+b_.*tan[c_.+d_.*x_]],x_Symbol] :=
  (A-C)*Int[Tan[c+d*x]^m/Sqrt[a+b*Tan[c+d*x]],x] + 
  C*Int[Tan[c+d*x]^m*(1+Tan[c+d*x]^2)/Sqrt[a+b*Tan[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)] && NonzeroQ[A-C]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)/Sqrt[a_+b_.*cot[c_.+d_.*x_]],x_Symbol] :=
  (A-C)*Int[Cot[c+d*x]^m/Sqrt[a+b*Cot[c+d*x]],x] + 
  C*Int[Cot[c+d*x]^m*(1+Cot[c+d*x]^2)/Sqrt[a+b*Cot[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2+b^2] && Not[RationalQ[m] && (m>0 || m<=-1)] && NonzeroQ[A-C]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) - 
  1/(b*(n+1)*(a^2+b^2))*Int[Tan[c+d*x]^(m-1)*(a+b*Tan[c+d*x])^(n+1)*
    Simp[m*(A*b^2-a*b*B+a^2*C)-b*(b*B+a*(A-C))*(n+1)*Tan[c+d*x]+(b*(A*b-a*B)*(m+n+1)+C*(a^2*m-b^2*(n+1)))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>0


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) - 
  1/(b*(n+1)*(a^2+b^2))*Int[Cot[c+d*x]^(m-1)*(a+b*Cot[c+d*x])^(n+1)*
    Simp[m*(A*b^2-a*b*B+a^2*C)-b*(b*B+a*(A-C))*(n+1)*Cot[c+d*x]+(b*(A*b-a*B)*(m+n+1)+C*(a^2*m-b^2*(n+1)))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>0


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) - 
  1/(b*(n+1)*(a^2+b^2))*Int[Tan[c+d*x]^(m-1)*(a+b*Tan[c+d*x])^(n+1)*
    Simp[m*(A*b^2+a^2*C)-a*b*(A-C)*(n+1)*Tan[c+d*x]+(A*b^2*(m+n+1)+C*(a^2*m-b^2*(n+1)))*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>0


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)*(a^2+b^2)) - 
  1/(b*(n+1)*(a^2+b^2))*Int[Cot[c+d*x]^(m-1)*(a+b*Cot[c+d*x])^(n+1)*
    Simp[m*(A*b^2+a^2*C)-a*b*(A-C)*(n+1)*Cot[c+d*x]+(A*b^2*(m+n+1)+C*(a^2*m-b^2*(n+1)))*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2+b^2] && RationalQ[m,n] && n<-1 && m>0


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n+1)/(a*d*(n+1)*(a^2+b^2)) + 
  1/(a*(n+1)*(a^2+b^2))*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)*
    Simp[A*(a^2*(n+1)+b^2*(m+n+2))-a*(b*B-a*C)*(m+1)+a*(a*B-b*(A-C))*(n+1)*Tan[c+d*x]+(A*b^2-a*b*B+a^2*C)*(m+n+2)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>0]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n+1)/(a*d*(n+1)*(a^2+b^2)) + 
  1/(a*(n+1)*(a^2+b^2))*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)*
    Simp[A*(a^2*(n+1)+b^2*(m+n+2))-a*(b*B-a*C)*(m+1)+a*(a*B-b*(A-C))*(n+1)*Cot[c+d*x]+(A*b^2-a*b*B+a^2*C)*(m+n+2)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>0]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Tan[c+d*x]^(m+1)*(a+b*Tan[c+d*x])^(n+1)/(a*d*(n+1)*(a^2+b^2)) + 
  1/(a*(n+1)*(a^2+b^2))*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^(n+1)*
    Simp[A*(a^2*(n+1)+b^2*(m+n+2))+a^2*C*(m+1)-a*b*(A-C)*(n+1)*Tan[c+d*x]+(A*b^2+a^2*C)*(m+n+2)*Tan[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>0]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Cot[c+d*x]^(m+1)*(a+b*Cot[c+d*x])^(n+1)/(a*d*(n+1)*(a^2+b^2)) + 
  1/(a*(n+1)*(a^2+b^2))*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^(n+1)*
    Simp[A*(a^2*(n+1)+b^2*(m+n+2))+a^2*C*(m+1)-a*b*(A-C)*(n+1)*Cot[c+d*x]+(A*b^2+a^2*C)*(m+n+2)*Cot[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>0]


Int[tan[c_.+d_.*x_]^m_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Tan[c+d*x]^m*(A+B*Tan[c+d*x])*(a+b*Tan[c+d*x])^n,x] + C*Int[Tan[c+d*x]^(m+2)*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x]


Int[cot[c_.+d_.*x_]^m_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cot[c+d*x]^m*(A+B*Cot[c+d*x])*(a+b*Cot[c+d*x])^n,x] + C*Int[Cot[c+d*x]^(m+2)*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x]


Int[tan[c_.+d_.*x_]^m_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Tan[c+d*x]^m*(a+b*Tan[c+d*x])^n,x] + C*Int[Tan[c+d*x]^(m+2)*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x]


Int[cot[c_.+d_.*x_]^m_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Cot[c+d*x]^m*(a+b*Cot[c+d*x])^n,x] + C*Int[Cot[c+d*x]^(m+2)*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x]


Int[(e_.*cot[c_.+d_.*x_])^m_*(A_.+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Cot[c+d*x])^m*Tan[c+d*x]^m*Int[(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2)/Tan[c+d*x]^m,x] /;
FreeQ[{c,d,e,A,B,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*tan[c_.+d_.*x_])^m_*(A_.+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Tan[c+d*x])^m*Cot[c+d*x]^m*Int[(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2)/Cot[c+d*x]^m,x] /;
FreeQ[{c,d,e,A,B,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_*(A_.+C_.*tan[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Cot[c+d*x])^m*Tan[c+d*x]^m*Int[(A+C*Tan[c+d*x]^2)/Tan[c+d*x]^m,x] /;
FreeQ[{c,d,e,A,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*tan[c_.+d_.*x_])^m_*(A_.+C_.*cot[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Tan[c+d*x])^m*Cot[c+d*x]^m*Int[(A+C*Cot[c+d*x]^2)/Cot[c+d*x]^m,x] /;
FreeQ[{c,d,e,A,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_.*(f_.*tan[c_.+d_.*x_])^p_.*(A_.+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Cot[c+d*x])^m*(f*Tan[c+d*x])^p/Tan[c+d*x]^(p-m)*Int[Tan[c+d*x]^(p-m)*(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,B,C,m,p},x]


Int[(e_.*tan[c_.+d_.*x_])^m_.*(f_.*cot[c_.+d_.*x_])^p_.*(A_.+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Tan[c+d*x])^m*(f*Cot[c+d*x])^p/Cot[c+d*x]^(p-m)*Int[Cot[c+d*x]^(p-m)*(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,B,C,m,p},x]


Int[(e_.*cot[c_.+d_.*x_])^m_.*(f_.*tan[c_.+d_.*x_])^p_.*(A_.+C_.*tan[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Cot[c+d*x])^m*(f*Tan[c+d*x])^p/Tan[c+d*x]^(p-m)*Int[Tan[c+d*x]^(p-m)*(A+C*Tan[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,C,m,p},x]


Int[(e_.*tan[c_.+d_.*x_])^m_.*(f_.*cot[c_.+d_.*x_])^p_.*(A_.+C_.*cot[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Tan[c+d*x])^m*(f*Cot[c+d*x])^p/Cot[c+d*x]^(p-m)*Int[Cot[c+d*x]^(p-m)*(A+C*Cot[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,C,m,p},x]


Int[(e_*tan[c_.+d_.*x_])^m_*(A_.+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m/Tan[c+d*x]^m*Int[Tan[c+d*x]^m*(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*cot[c_.+d_.*x_])^m_*(A_.+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m/Cot[c+d*x]^m*Int[Cot[c+d*x]^m*(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*tan[c_.+d_.*x_])^m_*(A_.+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m/Tan[c+d*x]^m*Int[Tan[c+d*x]^m*(A+C*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*cot[c_.+d_.*x_])^m_*(A_.+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m/Cot[c+d*x]^m*Int[Cot[c+d*x]^m*(A+C*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_*(A_.+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*Tan[c+d*x]^m*Int[(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^n/Tan[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*tan[c_.+d_.*x_])^m_*(A_.+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m*Cot[c+d*x]^m*Int[(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^n/Cot[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_*(A_.+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*Tan[c+d*x]^m*Int[(A+C*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^n/Tan[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*tan[c_.+d_.*x_])^m_*(A_.+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m*Cot[c+d*x]^m*Int[(A+C*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^n/Cot[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_])^m_.*(f_.*tan[c_.+d_.*x_])^p_.*(A_.+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*(f*Tan[c+d*x])^p/Tan[c+d*x]^(p-m)*Int[Tan[c+d*x]^(p-m)*(A+B*Tan[c+d*x]+C*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x]


Int[(e_.*tan[c_.+d_.*x_])^m_.*(f_.*cot[c_.+d_.*x_])^p_.*(A_.+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m*(f*Cot[c+d*x])^p/Cot[c+d*x]^(p-m)*Int[Cot[c+d*x]^(p-m)*(A+B*Cot[c+d*x]+C*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x]


Int[(e_.*cot[c_.+d_.*x_])^m_.*(f_.*tan[c_.+d_.*x_])^p_.*(A_.+C_.*tan[c_.+d_.*x_]^2)*(a_.+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*(f*Tan[c+d*x])^p/Tan[c+d*x]^(p-m)*Int[Tan[c+d*x]^(p-m)*(A+C*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n,p},x]


Int[(e_.*tan[c_.+d_.*x_])^m_.*(f_.*cot[c_.+d_.*x_])^p_.*(A_.+C_.*cot[c_.+d_.*x_]^2)*(a_.+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x])^m*(f*Cot[c+d*x])^p/Cot[c+d*x]^(p-m)*Int[Cot[c+d*x]^(p-m)*(A+C*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n,p},x]


Int[u_.*(A_+B_.*cot[c_.+d_.*x_]+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Tan[c+d*x]+A*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^n/Tan[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x]


Int[u_.*(A_+B_.*tan[c_.+d_.*x_]+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Cot[c+d*x]+A*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^n/Cot[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x]


Int[u_.*(A_+C_.*cot[c_.+d_.*x_]^2)*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Tan[c+d*x]^2)*(a+b*Tan[c+d*x])^n/Tan[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,C,n},x]


Int[u_.*(A_+C_.*tan[c_.+d_.*x_]^2)*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Cot[c+d*x]^2)*(a+b*Cot[c+d*x])^n/Cot[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,C,n},x]


(* ::Subsection::Closed:: *)
(*7.2.4 trig(c+d x)^m (a+b tan(c+d x))^n*)


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  e^(m+1)/d*Subst[Int[x^m*(a+b*e*x)^n/(1+e^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m/2]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_,x_Symbol] :=
  Module[{e=FreeFactors[Cot[c+d*x],x]},
  -e^(m+1)/d*Subst[Int[x^m*(a+b*e*x)^n/(1+e^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m/2]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Expand[Sin[c+d*x]^m*(a+b*Tan[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && PositiveIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Expand[Cos[c+d*x]^m*(a+b*Cot[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && PositiveIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sin[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/Cos[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && NegativeIntegerQ[n] && (m<5 && n>-4 || m==5 && n==-1)


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cos[c+d*x]^m*(a*Sin[c+d*x]+b*Cos[c+d*x])^n/Sin[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && NegativeIntegerQ[n] && (m<5 && n>-4 || m==5 && n==-1)


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Module[{e=FreeFactors[Tan[c+d*x],x]},
  e/d*Subst[Int[(a+b*e*x)^n/(1+e^2*x^2)^(m/2+1),x],x,Tan[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m/2]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Module[{e=FreeFactors[Cot[c+d*x],x]},
  -e/d*Subst[Int[(a+b*e*x)^n/(1+e^2*x^2)^(m/2+1),x],x,Cot[c+d*x]/e]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m/2]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Expand[Cos[c+d*x]^m*(a+b*Tan[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && PositiveIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Expand[Sin[c+d*x]^m*(a+b*Cot[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && PositiveIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cos[c+d*x]^(m-n)*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && NegativeIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sin[c+d*x]^(m-n)*(a*Sin[c+d*x]+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && NegativeIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^p_.*(a_+b_.*tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Cos[c+d*x]^(m-n)*Sin[c+d*x]^p*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,p},x] && IntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*cos[c_.+d_.*x_]^p_.*(a_+b_.*cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sin[c+d*x]^(m-n)*Cos[c+d*x]^p*(a*Sin[c+d*x]+b*Cos[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,p},x] && IntegerQ[n]


(* ::Subsection::Closed:: *)
(*7.3.1 sec(c+d x)^m (a+b sec(c+d x))^n*)


Int[sec[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  a*Int[Sec[c+d*x]^m,x] + b*Int[Sec[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,m},x]


Int[csc[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  a*Int[Csc[c+d*x]^m,x] + b*Int[Csc[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,m},x]


Int[sec[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_])^2,x_Symbol] :=
  2*a*b*Int[Sec[c+d*x]^(m+1),x] + Int[Sec[c+d*x]^m*(a^2+b^2*Sec[c+d*x]^2),x] /;
FreeQ[{a,b,c,d,m},x]


Int[csc[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_])^2,x_Symbol] :=
  2*a*b*Int[Csc[c+d*x]^(m+1),x] + Int[Csc[c+d*x]^m*(a^2+b^2*Csc[c+d*x]^2),x] /;
FreeQ[{a,b,c,d,m},x]


Int[sec[c_.+d_.*x_]/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  Int[1/(b+a*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[csc[c_.+d_.*x_]/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  Int[1/(b+a*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[sec[c_.+d_.*x_]^2/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[Sec[c+d*x],x] - 
  a/b*Int[Sec[c+d*x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[csc[c_.+d_.*x_]^2/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[Csc[c+d*x],x] - 
  a/b*Int[Csc[c+d*x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x]


Int[sec[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -Sin[c+d*x]*Sec[c+d*x]^(m-1)/(d*(a+b*Sec[c+d*x])) + 
  (m-1)/b*Int[Sec[c+d*x]^(m-1),x] - 
  (m-2)/a*Int[Sec[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[csc[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  Cos[c+d*x]*Csc[c+d*x]^(m-1)/(d*(a+b*Csc[c+d*x])) + 
  (m-1)/b*Int[Csc[c+d*x]^(m-1),x] - 
  (m-2)/a*Int[Csc[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[sec[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*(a+b*Sec[c+d*x])) - 
  (m-1)/a*Int[Sec[c+d*x]^m,x] + 
  m/b*Int[Sec[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<0


Int[csc[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*(a+b*Csc[c+d*x])) - 
  (m-1)/a*Int[Csc[c+d*x]^m,x] + 
  m/b*Int[Csc[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<0


Int[sec[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  a*Sin[c+d*x]*Sec[c+d*x]^m/(b*d*(a+b*Sec[c+d*x])) + 
  (m-1)/b*Int[Sec[c+d*x]^(m-1),x] - 
  (m-1)/a*Int[Sec[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -a*Cos[c+d*x]*Csc[c+d*x]^m/(b*d*(a+b*Csc[c+d*x])) + 
  (m-1)/b*Int[Csc[c+d*x]^(m-1),x] - 
  (m-1)/a*Int[Csc[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2]


Int[Sqrt[sec[c_.+d_.*x_]]/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  Sqrt[Sec[c+d*x]]*Sqrt[Cos[c+d*x]]*Int[Sqrt[Cos[c+d*x]]/(b+a*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[csc[c_.+d_.*x_]]/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  Sqrt[Csc[c+d*x]]*Sqrt[Sin[c+d*x]]*Int[Sqrt[Sin[c+d*x]]/(b+a*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^(3/2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  Sqrt[Sec[c+d*x]]*Sqrt[Cos[c+d*x]]*Int[1/(Sqrt[Cos[c+d*x]]*(b+a*Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^(3/2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  Sqrt[Csc[c+d*x]]*Sqrt[Sin[c+d*x]]*Int[1/(Sqrt[Sin[c+d*x]]*(b+a*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  Sin[c+d*x]*Sec[c+d*x]^(m-2)/(b*d*(m-2)) + 
  1/(b*(m-2))*Int[Sec[c+d*x]^(m-3)*Simp[a*(m-3)+b*(m-3)*Sec[c+d*x]-a*(m-2)*Sec[c+d*x]^2,x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>2 && IntegersQ[2*m]


Int[csc[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]*Csc[c+d*x]^(m-2)/(b*d*(m-2)) + 
  1/(b*(m-2))*Int[Csc[c+d*x]^(m-3)*Simp[a*(m-3)+b*(m-3)*Csc[c+d*x]-a*(m-2)*Csc[c+d*x]^2,x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>2 && IntegersQ[2*m]


Int[1/(Sqrt[sec[c_.+d_.*x_]]*(a_+b_.*sec[c_.+d_.*x_])),x_Symbol] :=
  Sqrt[Sec[c+d*x]]*Sqrt[Cos[c+d*x]]*Int[Cos[c+d*x]^(3/2)/(b+a*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[csc[c_.+d_.*x_]]*(a_+b_.*csc[c_.+d_.*x_])),x_Symbol] :=
  Sqrt[Csc[c+d*x]]*Sqrt[Sin[c+d*x]]*Int[Sin[c+d*x]^(3/2)/(b+a*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -Sin[c+d*x]*Sec[c+d*x]^(m+1)/(a*d*m) - 
  1/(a*m)*Int[Sec[c+d*x]^(m+1)*Simp[b*m-a*(m+1)*Sec[c+d*x]-b*(m+1)*Sec[c+d*x]^2,x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<=-1 && IntegerQ[2*m]


Int[csc[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  Cos[c+d*x]*Csc[c+d*x]^(m+1)/(a*d*m) - 
  1/(a*m)*Int[Csc[c+d*x]^(m+1)*Simp[b*m-a*(m+1)*Csc[c+d*x]-b*(m+1)*Csc[c+d*x]^2,x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<=-1 && IntegerQ[2*m]


Int[sec[c_.+d_.*x_]*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*b*Tan[c+d*x]/(d*Sqrt[a+b*Sec[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*b*Cot[c+d*x]/(d*Sqrt[a+b*Csc[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n-1)/(d*n) + 
  a*(2*n-1)/n*Int[Sec[c+d*x]*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2


Int[csc[c_.+d_.*x_]*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  a*(2*n-1)/n*Int[Csc[c+d*x]*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2


Int[sec[c_.+d_.*x_]/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*Rt[a,2]/(b*d)*ArcTan[Rt[a,2]*Tan[c+d*x]/(Sqrt[2]*Sqrt[a+b*Sec[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[a]


Int[csc[c_.+d_.*x_]/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*Rt[a,2]/(b*d)*ArcTan[Rt[a,2]*Cot[c+d*x]/(Sqrt[2]*Sqrt[a+b*Csc[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[a]


Int[sec[c_.+d_.*x_]/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*Rt[-a,2]/(b*d)*ArcTanh[Rt[-a,2]*Tan[c+d*x]/(Sqrt[2]*Sqrt[a+b*Sec[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[a]


Int[csc[c_.+d_.*x_]/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*Rt[-a,2]/(b*d)*ArcTanh[Rt[-a,2]*Cot[c+d*x]/(Sqrt[2]*Sqrt[a+b*Csc[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[a]


Int[sec[c_.+d_.*x_]*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(a*d*(2*n+1)) + 
  (n+1)/(a*(2*n+1))*Int[Sec[c+d*x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[csc[c_.+d_.*x_]*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(a*d*(2*n+1)) + 
  (n+1)/(a*(2*n+1))*Int[Csc[c+d*x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[sec[c_.+d_.*x_]*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b*Int[(a+b*Sec[c+d*x])^(n+1),x] - 
  a/b*Int[(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b*Int[(a+b*Csc[c+d*x])^(n+1),x] - 
  a/b*Int[(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^2*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(2*n+1)) + 
  n/(b*(2*n+1))*Int[Sec[c+d*x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[csc[c_.+d_.*x_]^2*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  n/(b*(2*n+1))*Int[Csc[c+d*x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[sec[c_.+d_.*x_]^2*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  b*n/(a*(n+1))*Int[Sec[c+d*x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<-1/2]


Int[csc[c_.+d_.*x_]^2*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  b*n/(a*(n+1))*Int[Csc[c+d*x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<-1/2]


Int[Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[a,2]/d*ArcSinh[Rt[a,2]*Tan[c+d*x]/Sqrt[a+b*Sec[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PosQ[a]


Int[Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[a,2]/d*ArcSinh[Rt[a,2]*Cot[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PosQ[a]


Int[Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[-a,2]/d*ArcSin[Rt[-a,2]*Tan[c+d*x]/Sqrt[a+b*Sec[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && NegQ[a]


Int[Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[-a,2]/d*ArcSin[Rt[-a,2]*Cot[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && NegQ[a]


Int[Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[b,2]/d*ArcTanh[Rt[b,2]*Sqrt[Sec[c+d*x]]*Sin[c+d*x]/Sqrt[a+b*Sec[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[b]


Int[Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[b,2]/d*ArcTanh[Rt[b,2]*Sqrt[Csc[c+d*x]]*Cos[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[b]


Int[Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -2*Rt[-b,2]/d*ArcTan[Rt[-b,2]*Sqrt[Sec[c+d*x]]*Sin[c+d*x]/Sqrt[a+b*Sec[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[b]


Int[Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[-b,2]/d*ArcTan[Rt[-b,2]*Sqrt[Csc[c+d*x]]*Cos[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[b]


Int[sec[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*b*Sin[c+d*x]*Sec[c+d*x]^m/(d*(2*m-1)*Sqrt[a+b*Sec[c+d*x]]) + 
  2*a*(m-1)/(b*(2*m-1))*Int[Sec[c+d*x]^(m-1)*Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2


Int[csc[c_.+d_.*x_]^m_*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*b*Cos[c+d*x]*Csc[c+d*x]^m/(d*(2*m-1)*Sqrt[a+b*Csc[c+d*x]]) + 
  2*a*(m-1)/(b*(2*m-1))*Int[Csc[c+d*x]^(m-1)*Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]]/Sqrt[sec[c_.+d_.*x_]],x_Symbol] :=
  2*a*Sin[c+d*x]*Sqrt[Sec[c+d*x]]/(d*Sqrt[a+b*Sec[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]]/Sqrt[csc[c_.+d_.*x_]],x_Symbol] :=
  -2*a*Cos[c+d*x]*Sqrt[Csc[c+d*x]]/(d*Sqrt[a+b*Csc[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -a*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Sec[c+d*x]]) + 
  b*(2*m+1)/(2*a*m)*Int[Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[csc[c_.+d_.*x_]^m_*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  a*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Csc[c+d*x]]) + 
  b*(2*m+1)/(2*a*m)*Int[Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[sec[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*a*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*Sqrt[a+b*Sec[c+d*x]]*(b/a*Sec[c+d*x])^m)*Hypergeometric2F1[1/2,1-m,3/2,1/a*(a-b*Sec[c+d*x])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^m_*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*a*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*Sqrt[a+b*Csc[c+d*x]]*(b/a*Csc[c+d*x])^m)*Hypergeometric2F1[1/2,1-m,3/2,1/a*(a-b*Csc[c+d*x])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-1)/(d*n) + 
  b*(2*n-1)/n*Int[Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1/2 && m+n==0


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  b*(2*n-1)/n*Int[Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1/2 && m+n==0


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  a*n/(b*(n+1))*Int[Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1/2 && m+n+1==0


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  a*n/(b*(n+1))*Int[Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1/2 && m+n+1==0


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-2)/(d*m) + 
  a/m*Int[Sec[c+d*x]^(m+1)*(b*(2*m-n+2)+a*(2*m+n-1)*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-2)/(d*m) + 
  a/m*Int[Csc[c+d*x]^(m+1)*(b*(2*m-n+2)+a*(2*m+n-1)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[(a_+b_.*sec[c_.+d_.*x_])^(3/2)/Sqrt[sec[c_.+d_.*x_]],x_Symbol] :=
  2*a^2*Sin[c+d*x]*Sqrt[Sec[c+d*x]]/(d*Sqrt[a+b*Sec[c+d*x]]) + 
  b*Int[Sqrt[Sec[c+d*x]]*Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^(3/2)/Sqrt[csc[c_.+d_.*x_]],x_Symbol] :=
  -2*a^2*Cos[c+d*x]*Sqrt[Csc[c+d*x]]/(d*Sqrt[a+b*Csc[c+d*x]]) + 
  b*Int[Sqrt[Csc[c+d*x]]*Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-2)/(d*(m+n-1)) + 
  a/(m+n-1)*Int[Sec[c+d*x]^m*(a*(2*m+n-1)+b*(2*m+3*n-4)*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n-1]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-2)/(d*(m+n-1)) + 
  a/(m+n-1)*Int[Csc[c+d*x]^m*(a*(2*m+n-1)+b*(2*m+3*n-4)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n-1]


(* Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Int[Sec[c+d*x]^m*(a+b*Sec[c+d*x])^(n-1),x] + 
  b*Int[Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2 *)


(* Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Int[Csc[c+d*x]^m*(a+b*Csc[c+d*x])^(n-1),x] + 
  b*Int[Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2 *)


Int[Sqrt[sec[c_.+d_.*x_]]/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]/(Sqrt[a]*d)*ArcSinh[Tan[c+d*x]/(1+Sec[c+d*x])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PositiveQ[a]


Int[Sqrt[csc[c_.+d_.*x_]]/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]/(Sqrt[a]*d)*ArcSinh[Cot[c+d*x]/(1+Csc[c+d*x])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PositiveQ[a]


Int[Sqrt[sec[c_.+d_.*x_]]/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*Rt[b,2]/(a*d)*ArcTanh[Rt[b,2]*Sqrt[Sec[c+d*x]]*Sin[c+d*x]/(Sqrt[2]*Sqrt[a+b*Sec[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[b]


Int[Sqrt[csc[c_.+d_.*x_]]/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*Rt[b,2]/(a*d)*ArcTanh[Rt[b,2]*Sqrt[Csc[c+d*x]]*Cos[c+d*x]/(Sqrt[2]*Sqrt[a+b*Csc[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && PosQ[b]


Int[Sqrt[sec[c_.+d_.*x_]]/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -Sqrt[2]*Rt[-b,2]/(a*d)*ArcTan[Rt[-b,2]*Sqrt[Sec[c+d*x]]*Sin[c+d*x]/(Sqrt[2]*Sqrt[a+b*Sec[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[b]


Int[Sqrt[csc[c_.+d_.*x_]]/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[2]*Rt[-b,2]/(a*d)*ArcTan[Rt[-b,2]*Sqrt[Csc[c+d*x]]*Cos[c+d*x]/(Sqrt[2]*Sqrt[a+b*Csc[c+d*x]])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && NegQ[b]


Int[sec[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  1/b*Int[Sqrt[Sec[c+d*x]]*Sqrt[a+b*Sec[c+d*x]],x] - 
  a/b*Int[Sqrt[Sec[c+d*x]]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  1/b*Int[Sqrt[Csc[c+d*x]]*Sqrt[a+b*Csc[c+d*x]],x] - 
  a/b*Int[Sqrt[Csc[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*Sin[c+d*x]*Sec[c+d*x]^(m-1)/(d*(2*m-3)*Sqrt[a+b*Sec[c+d*x]]) + 
  1/(b*(2*m-3))*Int[Sec[c+d*x]^(m-2)*(2*b*(m-2)-a*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>3/2


Int[csc[c_.+d_.*x_]^m_/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*Cos[c+d*x]*Csc[c+d*x]^(m-1)/(d*(2*m-3)*Sqrt[a+b*Csc[c+d*x]]) + 
  1/(b*(2*m-3))*Int[Csc[c+d*x]^(m-2)*(2*b*(m-2)-a*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>3/2


Int[1/(Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  2*Sin[c+d*x]*Sqrt[Sec[c+d*x]]/(d*Sqrt[a+b*Sec[c+d*x]]) - 
  a/b*Int[Sqrt[Sec[c+d*x]]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[1/(Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  -2*Cos[c+d*x]*Sqrt[Csc[c+d*x]]/(d*Sqrt[a+b*Csc[c+d*x]]) - 
  a/b*Int[Sqrt[Csc[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Sec[c+d*x]]) + 
  1/(2*b*m)*Int[Sec[c+d*x]^(m+1)*(a+b*(2*m+1)*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[csc[c_.+d_.*x_]^m_/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Csc[c+d*x]]) + 
  1/(2*b*m)*Int[Csc[c+d*x]^(m+1)*(a+b*(2*m+1)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[Sqrt[sec[c_.+d_.*x_]]/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -Sin[c+d*x]*Sec[c+d*x]^(3/2)/(2*d*(a+b*Sec[c+d*x])^(3/2)) + 
  3/(4*a)*Int[Sqrt[Sec[c+d*x]]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[Sqrt[csc[c_.+d_.*x_]]/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  Cos[c+d*x]*Csc[c+d*x]^(3/2)/(2*d*(a+b*Csc[c+d*x])^(3/2)) + 
  3/(4*a)*Int[Sqrt[Csc[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[Sqrt[sec[c_.+d_.*x_]]*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sin[c+d*x]*Sqrt[Sec[c+d*x]]*(a+b*Sec[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(2*b^2*(2*n+1))*Int[(b+a*(2*n+1)*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1)/Sqrt[Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[Sqrt[csc[c_.+d_.*x_]]*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cos[c+d*x]*Sqrt[Csc[c+d*x]]*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(2*b^2*(2*n+1))*Int[(b+a*(2*n+1)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1)/Sqrt[Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sin[c+d*x]*Sec[c+d*x]^m*(a+b*Sec[c+d*x])^n/(b*d*(2*n+1)) + 
  (n+1)/(b*(2*n+1))*Int[Sec[c+d*x]^(m-1)*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m+n==0


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cos[c+d*x]*Csc[c+d*x]^m*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  (n+1)/(b*(2*n+1))*Int[Csc[c+d*x]^(m-1)*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m+n==0


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(2*n+1)) + 
  n/(a*(2*n+1))*Int[Sec[c+d*x]^m*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m+n+1==0


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  n/(a*(2*n+1))*Int[Csc[c+d*x]^m*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m+n+1==0


Int[sec[c_.+d_.*x_]^(3/2)/(a_+b_.*sec[c_.+d_.*x_])^2,x_Symbol] :=
  a*Sin[c+d*x]*Sec[c+d*x]^(3/2)/(3*b*d*(a+b*Sec[c+d*x])^2) + 
  1/(6*a*b)*Int[Sqrt[Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^(3/2)/(a_+b_.*csc[c_.+d_.*x_])^2,x_Symbol] :=
  -a*Cos[c+d*x]*Csc[c+d*x]^(3/2)/(3*b*d*(a+b*Csc[c+d*x])^2) + 
  1/(6*a*b)*Int[Sqrt[Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


(* Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sin[c+d*x]*Sec[c+d*x]^m*(a+b*Sec[c+d*x])^n/(b*d*(2*n+1)) + 
  (n+1)/(2*a*b*(2*n+1))*Int[Sec[c+d*x]^(m-1)*(a+b*Sec[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && 2*m+n-1==0 *)


(* Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cos[c+d*x]*Csc[c+d*x]^m*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  (n+1)/(2*a*b*(2*n+1))*Int[Csc[c+d*x]^(m-1)*(a+b*Csc[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && 2*m+n-1==0 *)


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*Sec[c+d*x]^(m-1)*(a+b*Sec[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Sec[c+d*x]^(m-2)*(a*(m-2)-b*(m-n-2)*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m>1


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*Csc[c+d*x]^(m-1)*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Csc[c+d*x]^(m-2)*(a*(m-2)-b*(m-n-2)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m>1


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Sec[c+d*x]^m*(a*(m+2*n+1)-b*(m+n+1)*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2 && Not[RationalQ[m] && m>=1]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Csc[c+d*x]^m*(a*(m+2*n+1)-b*(m+n+1)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2 && Not[RationalQ[m] && m>=1]


Int[sec[c_.+d_.*x_]*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  (a+b)*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] - 
  b*Int[Sec[c+d*x]*(1-Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  (a+b)*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] - 
  b*Int[Csc[c+d*x]*(1-Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[b+a*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Sec[c+d*x]])*Int[1/(Sqrt[Cos[c+d*x]]*Sqrt[b+a*Cos[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]])*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[b+a*Sin[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[Sec[c+d*x]*Simp[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[csc[c_.+d_.*x_]*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[Csc[c+d*x]*Simp[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[sec[c_.+d_.*x_]/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  1/(a-b)*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] - 
  b/(a-b)*Int[Sec[c+d*x]*(1+Sec[c+d*x])/(a+b*Sec[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  1/(a-b)*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] - 
  b/(a-b)*Int[Csc[c+d*x]*(1+Csc[c+d*x])/(a+b*Csc[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*Int[Sec[c+d*x]*Simp[a*(n+1)-b*(n+2)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[csc[c_.+d_.*x_]*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*Int[Csc[c+d*x]*Simp[a*(n+1)-b*(n+2)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[sec[c_.+d_.*x_]^2/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] - 
  Int[Sec[c+d*x]*(1-Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^2/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] - 
  Int[Csc[c+d*x]*(1-Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^2*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  n/(n+1)*Int[Sec[c+d*x]*(b+a*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[csc[c_.+d_.*x_]^2*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  n/(n+1)*Int[Csc[c+d*x]*(b+a*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[sec[c_.+d_.*x_]^2/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -1/(a-b)*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] + 
  a/(a-b)*Int[Sec[c+d*x]*(1+Sec[c+d*x])/(a+b*Sec[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^2/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -1/(a-b)*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] + 
  a/(a-b)*Int[Csc[c+d*x]*(1+Csc[c+d*x])/(a+b*Csc[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^2*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  1/((n+1)*(a^2-b^2))*Int[Sec[c+d*x]*Simp[b*(n+1)-a*(n+2)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-3/2 && IntegerQ[2*n]


Int[csc[c_.+d_.*x_]^2*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  1/((n+1)*(a^2-b^2))*Int[Csc[c+d*x]*Simp[b*(n+1)-a*(n+2)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-3/2 && IntegerQ[2*n]


Int[Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  a*Int[Sqrt[Sec[c+d*x]]/Sqrt[a+b*Sec[c+d*x]],x] + 
  b*Int[Sec[c+d*x]^(3/2)/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  a*Int[Sqrt[Csc[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],x] + 
  b*Int[Csc[c+d*x]^(3/2)/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*Sin[c+d*x]*Sec[c+d*x]^(m-1)*Sqrt[a+b*Sec[c+d*x]]/(d*(2*m-1)) + 
  1/(2*m-1)*Int[Sec[c+d*x]^(m-2)*Simp[2*a*(m-2)+b*(2*m-3)*Sec[c+d*x]+a*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[csc[c_.+d_.*x_]^m_*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*Cos[c+d*x]*Csc[c+d*x]^(m-1)*Sqrt[a+b*Csc[c+d*x]]/(d*(2*m-1)) + 
  1/(2*m-1)*Int[Csc[c+d*x]^(m-2)*Simp[2*a*(m-2)+b*(2*m-3)*Csc[c+d*x]+a*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]]/sec[c_.+d_.*x_],x_Symbol] :=
  -b*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] + 
  Int[(a+b*Sec[c+d*x]+b*Sec[c+d*x]^2)/(Sec[c+d*x]*Sqrt[a+b*Sec[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]]/csc[c_.+d_.*x_],x_Symbol] :=
  -b*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] + 
  Int[(a+b*Csc[c+d*x]+b*Csc[c+d*x]^2)/(Csc[c+d*x]*Sqrt[a+b*Csc[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]]/Sqrt[sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[a+b*Sec[c+d*x]]/(Sqrt[Sec[c+d*x]]*Sqrt[b+a*Cos[c+d*x]])*Int[Sqrt[b+a*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]]/Sqrt[csc[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[a+b*Csc[c+d*x]]/(Sqrt[Csc[c+d*x]]*Sqrt[b+a*Sin[c+d*x]])*Int[Sqrt[b+a*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -Sin[c+d*x]*Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]]/(d*m) - 
  1/(2*m)*Int[Sec[c+d*x]^(m+1)*Simp[b-2*a*(m+1)*Sec[c+d*x]-b*(2*m+3)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[csc[c_.+d_.*x_]^m_*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Cos[c+d*x]*Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]]/(d*m) - 
  1/(2*m)*Int[Csc[c+d*x]^(m+1)*Simp[b-2*a*(m+1)*Csc[c+d*x]-b*(2*m+3)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[sec[c_.+d_.*x_]^3*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Sec[c+d*x]*Simp[b*(n+1)-a*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[csc[c_.+d_.*x_]^3*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Csc[c+d*x]*Simp[b*(n+1)-a*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  2*b*Sin[c+d*x]*Sec[c+d*x]^m*Sqrt[a+b*Sec[c+d*x]]/(d*(2*m+1)) + 
  1/(2*m+1)*
    Int[Sec[c+d*x]^(m-1)*Simp[2*a*b*(m-1)+(b^2*(2*m-1)+a^2*(2*m+1))*Sec[c+d*x]+2*a*b*(m+1)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[2*m]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*b*Cos[c+d*x]*Csc[c+d*x]^m*Sqrt[a+b*Csc[c+d*x]]/(d*(2*m+1)) + 
  1/(2*m+1)*
    Int[Csc[c+d*x]^(m-1)*Simp[2*a*b*(m-1)+(b^2*(2*m-1)+a^2*(2*m+1))*Csc[c+d*x]+2*a*b*(m+1)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[2*m]


Int[(a_+b_.*sec[c_.+d_.*x_])^(3/2)/sec[c_.+d_.*x_],x_Symbol] :=
  1/2*Int[(3*a*b-b*(a-2*b)*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] + 
  a/2*Int[(2*a+b*Sec[c+d*x]+b*Sec[c+d*x]^2)/(Sec[c+d*x]*Sqrt[a+b*Sec[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^(3/2)/csc[c_.+d_.*x_],x_Symbol] :=
  1/2*Int[(3*a*b-b*(a-2*b)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  a/2*Int[(2*a+b*Csc[c+d*x]+b*Csc[c+d*x]^2)/(Csc[c+d*x]*Sqrt[a+b*Csc[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[c_.+d_.*x_])^(3/2)/Sqrt[sec[c_.+d_.*x_]],x_Symbol] :=
  a*Int[Sqrt[a+b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]],x] + 
  b*Int[Sqrt[Sec[c+d*x]]*Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^(3/2)/Sqrt[csc[c_.+d_.*x_]],x_Symbol] :=
  a*Int[Sqrt[a+b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]],x] + 
  b*Int[Sqrt[Csc[c+d*x]]*Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -a*Sin[c+d*x]*Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]]/(d*m) + 
  1/(2*m)*Int[Sec[c+d*x]^(m+1)*Simp[a*b*(2*m-1)+2*(b^2*m+a^2*(m+1))*Sec[c+d*x]+a*b*(2*m+3)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  a*Cos[c+d*x]*Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]]/(d*m) + 
  1/(2*m)*Int[Csc[c+d*x]^(m+1)*Simp[a*b*(2*m-1)+2*(b^2*m+a^2*(m+1))*Csc[c+d*x]+a*b*(2*m+3)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-2)/(d*m) + 
  1/m*
    Int[Sec[c+d*x]^(m+1)*
      Simp[a^2*b*(2*m-n+2)+a*(a^2+(a^2+3*b^2)*m)*Sec[c+d*x]+b*(a^2*(n-1)+(a^2+b^2)*m)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>2 && m<-1 && IntegersQ[2*m,2*n]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-2)/(d*m) + 
  1/m*
    Int[Csc[c+d*x]^(m+1)*
      Simp[a^2*b*(2*m-n+2)+a*(a^2+(a^2+3*b^2)*m)*Csc[c+d*x]+b*(a^2*(n-1)+(a^2+b^2)*m)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>2 && m<-1 && IntegersQ[2*m,2*n]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-2)/(d*(m+n-1)) + 
  1/(m+n-1)*
    Int[Sec[c+d*x]^m*
      Simp[a*(b^2*m+a^2*(m+n-1))+b*(b^2*(m+n-2)+3*a^2*(m+n-1))*Sec[c+d*x]+a*b^2*(2*m+3*n-4)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>2 && m>=-1 && IntegersQ[2*m,2*n]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-2)/(d*(m+n-1)) + 
  1/(m+n-1)*
    Int[Csc[c+d*x]^m*
      Simp[a*(b^2*m+a^2*(m+n-1))+b*(b^2*(m+n-2)+3*a^2*(m+n-1))*Csc[c+d*x]+a*b^2*(2*m+3*n-4)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n-3),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>2 && m>=-1 && IntegersQ[2*m,2*n]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[Sec[c+d*x]^m,(a+b*Sec[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[n]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[Csc[c+d*x]^m,(a+b*Csc[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[n]


Int[Sqrt[sec[c_.+d_.*x_]]/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[Sec[c+d*x]]*Sqrt[b+a*Cos[c+d*x]]/Sqrt[a+b*Sec[c+d*x]]*Int[1/Sqrt[b+a*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[csc[c_.+d_.*x_]]/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[Csc[c+d*x]]*Sqrt[b+a*Sin[c+d*x]]/Sqrt[a+b*Csc[c+d*x]]*Int[1/Sqrt[b+a*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(sec[c_.+d_.*x_])^(3/2)/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[Sec[c+d*x]]*Sqrt[b+a*Cos[c+d*x]]/Sqrt[a+b*Sec[c+d*x]]*Int[Sec[c+d*x]/Sqrt[b+a*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(csc[c_.+d_.*x_])^(3/2)/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[Csc[c+d*x]]*Sqrt[b+a*Sin[c+d*x]]/Sqrt[a+b*Csc[c+d*x]]*Int[Csc[c+d*x]/Sqrt[b+a*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*Sin[c+d*x]*Sec[c+d*x]^(m-2)*Sqrt[a+b*Sec[c+d*x]]/(b*d*(2*m-3)) + 
  1/(b*(2*m-3))*
    Int[Sec[c+d*x]^(m-3)*Simp[2*a*(m-3)+b*(2*m-5)*Sec[c+d*x]-2*a*(m-2)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>2 && IntegerQ[2*m]


Int[csc[c_.+d_.*x_]^m_/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*Cos[c+d*x]*Csc[c+d*x]^(m-2)*Sqrt[a+b*Csc[c+d*x]]/(b*d*(2*m-3)) + 
  1/(b*(2*m-3))*
    Int[Csc[c+d*x]^(m-3)*Simp[2*a*(m-3)+b*(2*m-5)*Csc[c+d*x]-2*a*(m-2)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>2 && IntegerQ[2*m]


Int[1/(sec[c_.+d_.*x_]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  -b/(2*a)*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] + 
  1/(2*a)*Int[(2*a+b*Sec[c+d*x]+b*Sec[c+d*x]^2)/(Sec[c+d*x]*Sqrt[a+b*Sec[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(csc[c_.+d_.*x_]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  -b/(2*a)*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  1/(2*a)*Int[(2*a+b*Csc[c+d*x]+b*Csc[c+d*x]^2)/(Csc[c+d*x]*Sqrt[a+b*Csc[c+d*x]]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  1/a*Int[Sqrt[a+b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]],x] - 
  b/a*Int[Sqrt[Sec[c+d*x]]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  1/a*Int[Sqrt[a+b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]],x] - 
  b/a*Int[Sqrt[Csc[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -Sin[c+d*x]*Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]]/(a*d*m) + 
  1/(2*a*m)*
    Int[Sec[c+d*x]^(m+1)*Simp[-b*(2*m+1)+2*a*(m+1)*Sec[c+d*x]+b*(2*m+3)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[csc[c_.+d_.*x_]^m_/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Cos[c+d*x]*Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]]/(a*d*m) + 
  1/(2*a*m)*
    Int[Csc[c+d*x]^(m+1)*Simp[-b*(2*m+1)+2*a*(m+1)*Csc[c+d*x]+b*(2*m+3)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[Sqrt[sec[c_.+d_.*x_]]*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Sin[c+d*x]*Sqrt[Sec[c+d*x]]*(a+b*Sec[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  1/(2*(n+1)*(a^2-b^2))*Int[Simp[b-2*a*(n+1)*Sec[c+d*x]+b*(2*n+3)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1)/Sqrt[Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[Sqrt[csc[c_.+d_.*x_]]*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*Sqrt[Csc[c+d*x]]*(a+b*Csc[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  1/(2*(n+1)*(a^2-b^2))*Int[Simp[b-2*a*(n+1)*Csc[c+d*x]+b*(2*n+3)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1)/Sqrt[Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[sec[c_.+d_.*x_]^(3/2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*Sin[c+d*x]*Sqrt[Sec[c+d*x]]*(a+b*Sec[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/(2*(n+1)*(a^2-b^2))*
    Int[Simp[a-2*b*(n+1)*Sec[c+d*x]+a*(2*n+3)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1)/Sqrt[Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[csc[c_.+d_.*x_]^(3/2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*Cos[c+d*x]*Sqrt[Csc[c+d*x]]*(a+b*Csc[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/(2*(n+1)*(a^2-b^2))*
    Int[Simp[a-2*b*(n+1)*Csc[c+d*x]+a*(2*n+3)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1)/Sqrt[Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Sin[c+d*x]*Sec[c+d*x]^(m-2)*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]^(m-3)*Simp[a^2*(m-3)+a*b*(n+1)*Sec[c+d*x]-(a^2*(m-2)+b^2*(n+1))*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>2 && IntegersQ[2*m,2*n]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -a^2*Cos[c+d*x]*Csc[c+d*x]^(m-2)*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]^(m-3)*Simp[a^2*(m-3)+a*b*(n+1)*Csc[c+d*x]-(a^2*(m-2)+b^2*(n+1))*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>2 && IntegersQ[2*m,2*n]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]^m*
      Simp[a^2*(n+1)-b^2*(m+n+1)-a*b*(n+1)*Sec[c+d*x]+b^2*(m+n+2)*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m<0 && IntegersQ[2*m,2*n]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]^m*
      Simp[a^2*(n+1)-b^2*(m+n+1)-a*b*(n+1)*Csc[c+d*x]+b^2*(m+n+2)*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m<0 && IntegersQ[2*m,2*n]


Int[sec[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b*Int[Sec[c+d*x]^(m-1)*(a+b*Sec[c+d*x])^(n+1),x] - 
  a/b*Int[Sec[c+d*x]^(m-1)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m]


Int[csc[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b*Int[Csc[c+d*x]^(m-1)*(a+b*Csc[c+d*x])^(n+1),x] - 
  a/b*Int[Csc[c+d*x]^(m-1)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m]


Int[sec[c_.+d_.*x_]^m_.*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Sec[c+d*x]^m*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[csc[c_.+d_.*x_]^m_.*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Csc[c+d*x]^m*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(e_*sec[c_.+d_.*x_])^m_*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m/Sec[c+d*x]^m*Int[Sec[c+d*x]^m*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_*csc[c_.+d_.*x_])^m_*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m/Csc[c+d*x]^m*Int[Csc[c+d*x]^m*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m*Sec[c+d*x]^m*Int[(a+b*Sec[c+d*x])^n/Sec[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*sin[c_.+d_.*x_])^m_*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m*Csc[c+d*x]^m*Int[(a+b*Csc[c+d*x])^n/Csc[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_.*(f_.*sec[c_.+d_.*x_])^p_.*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m*(f*Sec[c+d*x])^p/Sec[c+d*x]^(p-m)*Int[Sec[c+d*x]^(p-m)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(e_.*sin[c_.+d_.*x_])^m_.*(f_.*csc[c_.+d_.*x_])^p_.*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m*(f*Csc[c+d*x])^p/Csc[c+d*x]^(p-m)*Int[Csc[c+d*x]^(p-m)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


(* ::Subsection::Closed:: *)
(*7.3.2 sec(c+d x)^m (A+B sec(c+d x)) (a+b sec(c+d x))^n*)


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_])*(b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Sec[c+d*x])*(b*Sec[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,n},x] && IntegerQ[m]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_])*(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Csc[c+d*x])*(b*Csc[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,n},x] && IntegerQ[m]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(b_*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]]*Int[Sec[c+d*x]^(m+n)*(A+B*Sec[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(b_*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]]*Int[Csc[c+d*x]^(m+n)*(A+B*Csc[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(b_*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Sec[c+d*x]]/Sqrt[b*Sec[c+d*x]]*Int[Sec[c+d*x]^(m+n)*(A+B*Sec[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(b_*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Csc[c+d*x]]/Sqrt[b*Csc[c+d*x]]*Int[Csc[c+d*x]^(m+n)*(A+B*Csc[c+d*x]),x] /;
FreeQ[{b,c,d,A,B},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(b_*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Sec[c+d*x])^n/Sec[c+d*x]^n*Int[Sec[c+d*x]^(m+n)*(A+B*Sec[c+d*x]),x] /;
FreeQ[{b,c,d,A,B,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(b_*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Csc[c+d*x])^n/Csc[c+d*x]^n*Int[Csc[c+d*x]^(m+n)*(A+B*Csc[c+d*x]),x] /;
FreeQ[{b,c,d,A,B,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[Sec[c+d*x]^m*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[A*b-a*B]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[Csc[c+d*x]^m*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[A*b-a*B]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -a*A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*m) + 
  1/m*Int[Sec[c+d*x]^(m+1)*Simp[(A*b+a*B)*m+(a*A*(m+1)+b*B*m)*Sec[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[m] && m<=-1


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  a*A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*m) + 
  1/m*Int[Csc[c+d*x]^(m+1)*Simp[(A*b+a*B)*m+(a*A*(m+1)+b*B*m)*Csc[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[m] && m<=-1


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  b*B*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*(m+1)) + 
  1/(m+1)*Int[Sec[c+d*x]^m*Simp[a*A*(m+1)+b*B*m+(A*b+a*B)*(m+1)*Sec[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[m] && m<=-1]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -b*B*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*(m+1)) + 
  1/(m+1)*Int[Csc[c+d*x]^m*Simp[a*A*(m+1)+b*B*m+(A*b+a*B)*(m+1)*Csc[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[m] && m<=-1]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  B*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[a^2-b^2] && ZeroQ[a*B*n+A*b*(n+1)]


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -B*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[a^2-b^2] && ZeroQ[a*B*n+A*b*(n+1)]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(a*d*(2*n+1)) + 
  (a*B*n+A*b*(n+1))/(a*b*(2*n+1))*Int[Sec[c+d*x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[a*B*n+A*b*(n+1)] && RationalQ[n] && n<-1/2


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(a*d*(2*n+1)) + 
  (a*B*n+A*b*(n+1))/(a*b*(2*n+1))*Int[Csc[c+d*x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[a*B*n+A*b*(n+1)] && RationalQ[n] && n<-1/2


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  B*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  (a*B*n+A*b*(n+1))/(b*(n+1))*Int[Sec[c+d*x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[a*B*n+A*b*(n+1)] && Not[RationalQ[n] && n<-1/2]


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  (a*B*n+A*b*(n+1))/(b*(n+1))*Int[Csc[c+d*x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[a*B*n+A*b*(n+1)] && Not[RationalQ[n] && n<-1/2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(n+1)) /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && ZeroQ[A*b*n-a*B*m]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(n+1)) /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && ZeroQ[A*b*n-a*B*m]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(b*d*(2*n+1)) - 
  (a*B*m-A*b*n)/(a*b*(2*n+1))*Int[Sec[c+d*x]^m*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && NonzeroQ[a*B*m-A*b*n] && RationalQ[n] && n<-1/2


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) - 
  (a*B*m-A*b*n)/(a*b*(2*n+1))*Int[Csc[c+d*x]^m*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && NonzeroQ[a*B*m-A*b*n] && RationalQ[n] && n<-1/2


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(n+1)) - 
  (a*B*m-A*b*n)/(a*(n+1))*Int[Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && NonzeroQ[a*B*m-A*b*n] && Not[RationalQ[n] && n<-1/2]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(n+1)) - 
  (a*B*m-A*b*n)/(a*(n+1))*Int[Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && NonzeroQ[a*B*m-A*b*n] && Not[RationalQ[n] && n<-1/2]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -a*A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Sec[c+d*x]]) /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[2*a*B*m+A*b*(2*m+1)]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  a*A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Csc[c+d*x]]) /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[2*a*B*m+A*b*(2*m+1)]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -a*A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Sec[c+d*x]]) + 
  (2*a*B*m+A*b*(2*m+1))/(2*a*m)*Int[Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[2*a*B*m+A*b*(2*m+1)] && RationalQ[m] && m<=-1/2


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  a*A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Csc[c+d*x]]) + 
  (2*a*B*m+A*b*(2*m+1))/(2*a*m)*Int[Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[2*a*B*m+A*b*(2*m+1)] && RationalQ[m] && m<=-1/2


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*b*B*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*(2*m+1)*Sqrt[a+b*Sec[c+d*x]]) + 
  (2*a*B*m+A*b*(2*m+1))/(b*(2*m+1))*Int[Sec[c+d*x]^m*Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[2*a*B*m+A*b*(2*m+1)] && Not[RationalQ[m] && m<=-1/2]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*b*B*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*(2*m+1)*Sqrt[a+b*Csc[c+d*x]]) + 
  (2*a*B*m+A*b*(2*m+1))/(b*(2*m+1))*Int[Csc[c+d*x]^m*Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[2*a*B*m+A*b*(2*m+1)] && Not[RationalQ[m] && m<=-1/2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-1)/(d*m) + 
  1/m*Int[Sec[c+d*x]^(m+1)*Simp[(A*b+a*B)*m-A*b*(n-1)+(a*A*n+(a*A+b*B)*m)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1/2 && m<-1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-1)/(d*m) + 
  1/m*Int[Csc[c+d*x]^(m+1)*Simp[(A*b+a*B)*m-A*b*(n-1)+(a*A*n+(a*A+b*B)*m)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n>1/2 && m<-1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  b*B*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-1)/(d*(m+n)) + 
  1/(m+n)*Int[Sec[c+d*x]^m*Simp[a*A*n+(a*A+b*B)*m+(A*b+a*B*n+(A*b+a*B)*(m+n-1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2 && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -b*B*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-1)/(d*(m+n)) + 
  1/(m+n)*Int[Csc[c+d*x]^m*Simp[a*A*n+(a*A+b*B)*m+(A*b+a*B*n+(A*b+a*B)*(m+n-1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2 && Not[RationalQ[m] && m<-1] && NonzeroQ[m+n]


Int[Sqrt[sec[c_.+d_.*x_]]*(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  B/b*Int[Sqrt[Sec[c+d*x]]*Sqrt[a+b*Sec[c+d*x]],x] + 
  (A*b-a*B)/b*Int[Sqrt[Sec[c+d*x]]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[Sqrt[csc[c_.+d_.*x_]]*(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  B/b*Int[Sqrt[Csc[c+d*x]]*Sqrt[a+b*Csc[c+d*x]],x] + 
  (A*b-a*B)/b*Int[Sqrt[Csc[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*B*Sin[c+d*x]*Sec[c+d*x]^m/(d*(2*m-1)*Sqrt[a+b*Sec[c+d*x]]) + 
  1/(a*(2*m-1))*Int[Sec[c+d*x]^(m-1)*Simp[2*a*B*(m-1)-(b*B-a*A*(2*m-1))*Sec[c+d*x],x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cos[c+d*x]*Csc[c+d*x]^m/(d*(2*m-1)*Sqrt[a+b*Csc[c+d*x]]) + 
  1/(a*(2*m-1))*Int[Csc[c+d*x]^(m-1)*Simp[2*a*B*(m-1)-(b*B-a*A*(2*m-1))*Csc[c+d*x],x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Sec[c+d*x]]) + 
  1/(2*a*m)*Int[Sec[c+d*x]^(m+1)*Simp[2*a*B*m+A*b+a*A*(2*m+1)*Sec[c+d*x],x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<=-1/2


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*m*Sqrt[a+b*Csc[c+d*x]]) + 
  1/(2*a*m)*Int[Csc[c+d*x]^(m+1)*Simp[2*a*B*m+A*b+a*A*(2*m+1)*Csc[c+d*x],x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<=-1/2


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Sin[c+d*x]*Sec[c+d*x]^m*(a+b*Sec[c+d*x])^n/(a*d*(2*n+1)) - 
  1/(a^2*(2*n+1))*
    Int[Sec[c+d*x]^(m-1)*Simp[(A*b-a*B)*(m-1)-(b*B*n+a*A*(n+1)+(a*A-b*B)*(m-1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m>0


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Cos[c+d*x]*Csc[c+d*x]^m*(a+b*Csc[c+d*x])^n/(a*d*(2*n+1)) - 
  1/(a^2*(2*n+1))*
    Int[Csc[c+d*x]^(m-1)*Simp[(A*b-a*B)*(m-1)-(b*B*n+a*A*(n+1)+(a*A-b*B)*(m-1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && n<-1/2 && m>0


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(b^2*(2*n+1))*
    Int[Sec[c+d*x]^m*Simp[a*A*(2*n+1)+(a*A-b*B)*m-(A*b-a*B)*(m+n+1)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(b^2*(2*n+1))*
    Int[Csc[c+d*x]^m*Simp[a*A*(2*n+1)+(a*A-b*B)*m-(A*b-a*B)*(m+n+1)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -2*A*Sin[c+d*x]*Sqrt[a+b*Sec[c+d*x]]/(b*d*(1+Cos[c+d*x])) + 
  2*A/b*Int[Sqrt[a+b*Sec[c+d*x]]/(1+Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A+B]


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  2*A*Cos[c+d*x]*Sqrt[a+b*Csc[c+d*x]]/(b*d*(1+Sin[c+d*x])) + 
  2*A/b*Int[Sqrt[a+b*Csc[c+d*x]]/(1+Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A+B]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  (A+B)*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] - 
  B*Int[Sec[c+d*x]*(1-Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && NonzeroQ[A+B]


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  (A+B)*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] - 
  B*Int[Csc[c+d*x]*(1-Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && NonzeroQ[A+B]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  B*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  1/(n+1)*Int[Sec[c+d*x]*Simp[b*B*n+a*A*(n+1)+(a*B*n+A*b*(n+1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -B*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  1/(n+1)*Int[Csc[c+d*x]*Simp[b*B*n+a*A*(n+1)+(a*B*n+A*b*(n+1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  B/b*Int[Sec[c+d*x],x] + (A*b-a*B)/b*Int[Sec[c+d*x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  B/b*Int[Csc[c+d*x],x] + (A*b-a*B)/b*Int[Csc[c+d*x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -2*A*(a-b)*Sin[c+d*x]/(b*(a+b)*d*Sqrt[a+b*Sec[c+d*x]]*(1+Cos[c+d*x])) + 
  2*A/(b*(a+b))*Int[Sqrt[a+b*Sec[c+d*x]]/(1+Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B]


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  2*A*(a-b)*Cos[c+d*x]/(b*(a+b)*d*Sqrt[a+b*Csc[c+d*x]]*(1+Sin[c+d*x])) + 
  2*A/(b*(a+b))*Int[Sqrt[a+b*Csc[c+d*x]]/(1+Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  (A-B)/(a-b)*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] - 
  (A*b-a*B)/(a-b)*Int[Sec[c+d*x]*(1+Sec[c+d*x])/(a+b*Sec[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  (A-B)/(a-b)*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] - 
  (A*b-a*B)/(a-b)*Int[Csc[c+d*x]*(1+Csc[c+d*x])/(a+b*Csc[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]*Simp[(a*A-b*B)*(n+1)-(A*b-a*B)*(n+2)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]*Simp[(a*A-b*B)*(n+1)-(A*b-a*B)*(n+2)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]]/Sqrt[sec[c_.+d_.*x_]],x_Symbol] :=
  A*Int[Sqrt[a+b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]],x] + 
  B*Int[Sqrt[Sec[c+d*x]]*Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]]/Sqrt[csc[c_.+d_.*x_]],x_Symbol] :=
  A*Int[Sqrt[a+b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]],x] + 
  B*Int[Sqrt[Csc[c+d*x]]*Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*B*Sin[c+d*x]*Sec[c+d*x]^m*Sqrt[a+b*Sec[c+d*x]]/(d*(2*m+1)) + 
  1/(2*m+1)*
    Int[Sec[c+d*x]^(m-1)*
      Simp[2*a*B*(m-1)+(2*a*A+(a*A+b*B)*(2*m-1))*Sec[c+d*x]+((A*b+a*B)+2*A*b*m)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cos[c+d*x]*Csc[c+d*x]^m*Sqrt[a+b*Csc[c+d*x]]/(d*(2*m+1)) + 
  1/(2*m+1)*
    Int[Csc[c+d*x]^(m-1)*
      Simp[2*a*B*(m-1)+(2*a*A+(a*A+b*B)*(2*m-1))*Csc[c+d*x]+((A*b+a*B)+2*A*b*m)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]]/sec[c_.+d_.*x_],x_Symbol] :=
  1/2*Int[(A*b+2*a*B-b*(A-2*B)*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] + 
  A/2*Int[(2*a+b*Sec[c+d*x]+b*Sec[c+d*x]^2)/(Sec[c+d*x]*Sqrt[a+b*Sec[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[A*b-a*B]


Int[(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]]/csc[c_.+d_.*x_],x_Symbol] :=
  1/2*Int[(A*b+2*a*B-b*(A-2*B)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  A/2*Int[(2*a+b*Csc[c+d*x]+b*Csc[c+d*x]^2)/(Csc[c+d*x]*Sqrt[a+b*Csc[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[A*b-a*B]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]]/(d*m) + 
  1/(2*m)*Int[Sec[c+d*x]^(m+1)*Simp[2*a*B*m-A*b+2*(a*A+(a*A+b*B)*m)*Sec[c+d*x]+A*b*(2*m+3)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]]/(d*m) + 
  1/(2*m)*Int[Csc[c+d*x]^(m+1)*Simp[2*a*B*m-A*b+2*(a*A+(a*A+b*B)*m)*Csc[c+d*x]+A*b*(2*m+3)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-1)/(d*m) + 
  1/m*
    Int[Sec[c+d*x]^(m+1)*
      Simp[a*((A*b+a*B)*m-A*b*(n-1))+(a^2*A+(a^2*A+2*a*b*B+b^2*A)*m)*Sec[c+d*x]+b*(a*A*n+(a*A+b*B)*m)*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-1)/(d*m) + 
  1/m*
    Int[Csc[c+d*x]^(m+1)*
      Simp[a*((A*b+a*B)*m-A*b*(n-1))+(a^2*A+(a^2*A+2*a*b*B+b^2*A)*m)*Csc[c+d*x]+b*(a*A*n+(a*A+b*B)*m)*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>1 && m<-1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  b*B*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n-1)/(d*(m+n)) + 
  1/(m+n)*
    Int[Sec[c+d*x]^m*
      Simp[a*(a*A*n+(a*A+b*B)*m)+(a*(2*A*b+a*B)+(a^2*B+2*a*A*b+b^2*B)*(m+n-1))*Sec[c+d*x]+
        b*(a*B*(n-1)+(A*b+a*B)*(m+n))*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -b*B*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n-1)/(d*(m+n)) + 
  1/(m+n)*
    Int[Csc[c+d*x]^m*
      Simp[a*(a*A*n+(a*A+b*B)*m)+(a*(2*A*b+a*B)+(a^2*B+2*a*A*b+b^2*B)*(m+n-1))*Csc[c+d*x]+
        b*(a*B*(n-1)+(A*b+a*B)*(m+n))*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[RationalQ[m] && m<-1]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  B*Sin[c+d*x]*Sec[c+d*x]^(m-1)/(b*d*(m-1)) + 
  1/(b*(m-1))*Int[Sec[c+d*x]^(m-2)*Simp[a*B*(m-2)+b*B*(m-2)*Sec[c+d*x]+(A*b-a*B)*(m-1)*Sec[c+d*x]^2,x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -B*Cos[c+d*x]*Csc[c+d*x]^(m-1)/(b*d*(m-1)) + 
  1/(b*(m-1))*Int[Csc[c+d*x]^(m-2)*Simp[a*B*(m-2)+b*B*(m-2)*Csc[c+d*x]+(A*b-a*B)*(m-1)*Csc[c+d*x]^2,x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(a*d*m) + 
  1/(a*m)*Int[Sec[c+d*x]^(m+1)*Simp[(a*B-A*b)*m+a*A*(m+1)*Sec[c+d*x]+A*b*(m+1)*Sec[c+d*x]^2,x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<=-1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(a*d*m) + 
  1/(a*m)*Int[Csc[c+d*x]^(m+1)*Simp[(a*B-A*b)*m+a*A*(m+1)*Csc[c+d*x]+A*b*(m+1)*Csc[c+d*x]^2,x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<=-1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  A/a*Int[Sec[c+d*x]^m,x] - (A*b-a*B)/a*Int[Sec[c+d*x]^(m+1)/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  A/a*Int[Csc[c+d*x]^m,x] - (A*b-a*B)/a*Int[Csc[c+d*x]^(m+1)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[sec[c_.+d_.*x_]]*(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  A*Int[Sqrt[Sec[c+d*x]]/Sqrt[a+b*Sec[c+d*x]],x] + 
  B*Int[Sec[c+d*x]^(3/2)/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[csc[c_.+d_.*x_]]*(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Int[Sqrt[Csc[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],x] + 
  B*Int[Csc[c+d*x]^(3/2)/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_])/(Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]],x] - 
  (A*b-a*B)/a*Int[Sqrt[Sec[c+d*x]]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])/(Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]],x] - 
  (A*b-a*B)/a*Int[Sqrt[Csc[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*B*Sin[c+d*x]*Sec[c+d*x]^(m-1)*Sqrt[a+b*Sec[c+d*x]]/(b*d*(2*m-1)) + 
  1/(b*(2*m-1))*
    Int[Sec[c+d*x]^(m-2)*Simp[2*a*B*(m-2)+b*B*(2*m-3)*Sec[c+d*x]+(A*b+2*(A*b-a*B)*(m-1))*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*B*Cos[c+d*x]*Csc[c+d*x]^(m-1)*Sqrt[a+b*Csc[c+d*x]]/(b*d*(2*m-1)) + 
  1/(b*(2*m-1))*
    Int[Csc[c+d*x]^(m-2)*Simp[2*a*B*(m-2)+b*B*(2*m-3)*Csc[c+d*x]+(A*b+2*(A*b-a*B)*(m-1))*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[(A_+B_.*sec[c_.+d_.*x_])/(sec[c_.+d_.*x_]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  -1/(2*a)*Int[(A*b-2*a*B+A*b*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] + 
  A/(2*a)*Int[(2*a+b*Sec[c+d*x]+b*Sec[c+d*x]^2)/(Sec[c+d*x]*Sqrt[a+b*Sec[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_])/(csc[c_.+d_.*x_]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  -1/(2*a)*Int[(A*b-2*a*B+A*b*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  A/(2*a)*Int[(2*a+b*Csc[c+d*x]+b*Csc[c+d*x]^2)/(Csc[c+d*x]*Sqrt[a+b*Csc[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]]/(a*d*m) + 
  1/(2*a*m)*
    Int[Sec[c+d*x]^(m+1)*Simp[2*(a*B-A*b)*m-A*b+2*a*A*(m+1)*Sec[c+d*x]+A*b*(2*m+3)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]]/(a*d*m) + 
  1/(2*a*m)*
    Int[Csc[c+d*x]^(m+1)*Simp[2*(a*B-A*b)*m-A*b+2*a*A*(m+1)*Csc[c+d*x]+A*b*(2*m+3)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[Sqrt[sec[c_.+d_.*x_]]*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B)*Sin[c+d*x]*Sqrt[Sec[c+d*x]]*(a+b*Sec[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/(2*(n+1)*(a^2-b^2))*
    Int[Simp[-(A*b-a*B)+2*(a*A-b*B)*(n+1)*Sec[c+d*x]-(A*b-a*B)*(2*n+3)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1)/Sqrt[Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[Sqrt[csc[c_.+d_.*x_]]*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B)*Cos[c+d*x]*Sqrt[Csc[c+d*x]]*(a+b*Csc[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/(2*(n+1)*(a^2-b^2))*
    Int[Simp[-(A*b-a*B)+2*(a*A-b*B)*(n+1)*Csc[c+d*x]-(A*b-a*B)*(2*n+3)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1)/Sqrt[Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(A*b-a*B)*Sin[c+d*x]*Sec[c+d*x]^(m-1)*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) - 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]^(m-2)*
      Simp[a*(A*b-a*B)*(m-2)+b*(A*b-a*B)*(n+1)*Sec[c+d*x]-(b*(a*A-b*B)*(n+1)+a*(A*b-a*B)*(m-1))*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(A*b-a*B)*Cos[c+d*x]*Csc[c+d*x]^(m-1)*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) - 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]^(m-2)*
      Simp[a*(A*b-a*B)*(m-2)+b*(A*b-a*B)*(n+1)*Csc[c+d*x]-(b*(a*A-b*B)*(n+1)+a*(A*b-a*B)*(m-1))*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(A*b-a*B)*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-b*(A*b-a*B)*m-a*(A*b-a*B)*(n+1)*Sec[c+d*x]+b*(A*b-a*B)*(m+n+2)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>1]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(A*b-a*B)*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-b*(A*b-a*B)*m-a*(A*b-a*B)*(n+1)*Csc[c+d*x]+b*(A*b-a*B)*(m+n+2)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>1]


(* Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_])*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Sec[c+d*x]^m*(a+b*Sec[c+d*x])^n,x] + B*Int[Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] *)


(* Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_])*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Csc[c+d*x]^m*(a+b*Csc[c+d*x])^n,x] + B*Int[Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x] *)


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_])*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Sec[c+d*x]^m*(A+B*Sec[c+d*x])*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_])*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][Csc[c+d*x]^m*(A+B*Csc[c+d*x])*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,m,n},x]


Int[(e_*sec[c_.+d_.*x_])^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m/Sec[c+d*x]^m*Int[Sec[c+d*x]^m*(A+B*Sec[c+d*x])*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_*csc[c_.+d_.*x_])^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m/Csc[c+d*x]^m*Int[Csc[c+d*x]^m*(A+B*Csc[c+d*x])*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_*(A_+B_.*sec[c_.+d_.*x_])*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m*Sec[c+d*x]^m*Int[(A+B*Sec[c+d*x])*(a+b*Sec[c+d*x])^n/Sec[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*sin[c_.+d_.*x_])^m_*(A_+B_.*csc[c_.+d_.*x_])*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m*Csc[c+d*x]^m*Int[(A+B*Csc[c+d*x])*(a+b*Csc[c+d*x])^n/Csc[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_.*(f_.*sec[c_.+d_.*x_])^p_.*(A_.+B_.*sec[c_.+d_.*x_])*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m*(f*Sec[c+d*x])^p/Sec[c+d*x]^(p-m)*Int[Sec[c+d*x]^(p-m)*(A+B*Sec[c+d*x])*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x]


Int[(e_.*sin[c_.+d_.*x_])^m_.*(f_.*csc[c_.+d_.*x_])^p_.*(A_.+B_.*csc[c_.+d_.*x_])*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m*(f*Csc[c+d*x])^p/Csc[c+d*x]^(p-m)*Int[Csc[c+d*x]^(p-m)*(A+B*Csc[c+d*x])*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x]


Int[u_.*(A_+B_.*cos[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Sec[c+d*x])*(a+b*Sec[c+d*x])^n/Sec[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B,n},x]


Int[u_.*(A_+B_.*sin[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Csc[c+d*x])*(a+b*Csc[c+d*x])^n/Csc[c+d*x],x] /;
FreeQ[{a,b,c,d,A,B,n},x]


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]]/(A_+B_.*cos[c_.+d_.*x_]),x_Symbol] :=
  Sqrt[b+a*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Sec[c+d*x]])*
    Int[Sqrt[b+a*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*(A+A*Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]]/(A_+B_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]])*
    Int[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(A+A*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[B-A] && NonzeroQ[a^2-b^2]


(* ::Subsection::Closed:: *)
(*7.3.3 sec(c+d x)^m (A+B sec(c+d x)+C sec(c+d x)^2) (a+b sec(c+d x))^n*)


Int[(B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sec[c+d*x]*(B+C*Sec[c+d*x])*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,n},x]


Int[(B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Csc[c+d*x]*(B+C*Csc[c+d*x])*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,n},x]


Int[sec[c_.+d_.*x_]^m_.*(B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Sec[c+d*x]^(m+1)*(B+C*Sec[c+d*x])*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,m,n},x]


Int[csc[c_.+d_.*x_]^m_.*(B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[Csc[c+d*x]^(m+1)*(B+C*Csc[c+d*x])*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,B,C,m,n},x]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  -A*Tan[c+d*x]*(b*Sec[c+d*x])^n/(d*n) /;
FreeQ[{b,c,d,A,C,n},x] && ZeroQ[A+n*(A+C)]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Cot[c+d*x]*(b*Csc[c+d*x])^n/(d*n) /;
FreeQ[{b,c,d,A,C,n},x] && ZeroQ[A+n*(A+C)]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  -A*Tan[c+d*x]*(b*Sec[c+d*x])^n/(d*n) + 
  (A+n*(A+C))/(b^2*n)*Int[(b*Sec[c+d*x])^(n+2),x] /;
FreeQ[{b,c,d,A,C},x] && NonzeroQ[A+n*(A+C)] && RationalQ[n] && n<=-1


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Cot[c+d*x]*(b*Csc[c+d*x])^n/(d*n) + 
  (A+n*(A+C))/(b^2*n)*Int[(b*Csc[c+d*x])^(n+2),x] /;
FreeQ[{b,c,d,A,C},x] && NonzeroQ[A+n*(A+C)] && RationalQ[n] && n<=-1


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*Tan[c+d*x]*(b*Sec[c+d*x])^n/(d*(n+1)) + 
  (A+n*(A+C))/(n+1)*Int[(b*Sec[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,C,n},x] && NonzeroQ[A+n*(A+C)] && Not[RationalQ[n] && n<=-1]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*Cot[c+d*x]*(b*Csc[c+d*x])^n/(d*(n+1)) + 
  (A+n*(A+C))/(n+1)*Int[(b*Csc[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,C,n},x] && NonzeroQ[A+n*(A+C)] && Not[RationalQ[n] && n<=-1]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/sec[c_.+d_.*x_],x_Symbol] :=
  B*x + Int[(A+C*Sec[c+d*x]^2)/Sec[c+d*x],x] /;
FreeQ[{c,d,A,B,C},x]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/csc[c_.+d_.*x_],x_Symbol] :=
  B*x + Int[(A+C*Csc[c+d*x]^2)/Csc[c+d*x],x] /;
FreeQ[{c,d,A,B,C},x]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(b*Sec[c+d*x])^(n+1),x] + 
  Int[(A+C*Sec[c+d*x]^2)*(b*Sec[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,B,C,n},x] && NonzeroQ[n+1]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  B/b*Int[(b*Csc[c+d*x])^(n+1),x] + 
  Int[(A+C*Csc[c+d*x]^2)*(b*Csc[c+d*x])^n,x] /;
FreeQ[{b,c,d,A,B,C,n},x] && NonzeroQ[n+1]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/b^2*Int[(b*B-a*C+b*C*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/b^2*Int[(b*B-a*C+b*C*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C/b^2*Int[(a-b*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[A*b^2+a^2*C]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C/b^2*Int[(a-b*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[A*b^2+a^2*C]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  C/b*Int[Sec[c+d*x],x] + 
  1/b*Int[(A*b+(b*B-a*C)*Sec[c+d*x])/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  C/b*Int[Csc[c+d*x],x] + 
  1/b*Int[(A*b+(b*B-a*C)*Csc[c+d*x])/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  C/b*Int[Sec[c+d*x],x] + 
  1/b*Int[(A*b-a*C*Sec[c+d*x])/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  C/b*Int[Csc[c+d*x],x] + 
  1/b*Int[(A*b-a*C*Csc[c+d*x])/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B+b*C)*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[a*A*(2*n+1)+(b*C*n-(b*A-a*B)*(n+1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B+b*C)*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[a*A*(2*n+1)+(b*C*n-(b*A-a*B)*(n+1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A+C)*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[a*A*(2*n+1)+(b*C*n-b*A*(n+1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A+C)*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Simp[a*A*(2*n+1)+(b*C*n-b*A*(n+1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  1/(a*(n+1))*Int[Simp[A*a*(n+1)+(b*C*n+a*B*(n+1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  1/(a*(n+1))*Int[Simp[A*a*(n+1)+(b*C*n+a*B*(n+1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  1/(a*(n+1))*Int[Simp[A*a*(n+1)+b*C*n*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  1/(a*(n+1))*Int[Simp[A*a*(n+1)+b*C*n*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  1/(n+1)*Int[Simp[a*A*(n+1)+(b*C*n+(A*b+a*B)*(n+1))*Sec[c+d*x]+(a*C*n+b*B*(n+1))*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  1/(n+1)*Int[Simp[a*A*(n+1)+(b*C*n+(A*b+a*B)*(n+1))*Csc[c+d*x]+(a*C*n+b*B*(n+1))*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  C*Tan[c+d*x]*(a+b*Sec[c+d*x])^n/(d*(n+1)) + 
  1/(n+1)*Int[Simp[a*A*(n+1)+b*(A+n*(A+C))*Sec[c+d*x]+a*C*n*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  1/(n+1)*Int[Simp[a*A*(n+1)+b*(A+n*(A+C))*Csc[c+d*x]+a*C*n*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  A*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  Int[Sec[c+d*x]*(A-B-C*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  Int[Csc[c+d*x]*(A-B-C*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  A*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  Int[Sec[c+d*x]*(A-C*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  Int[Csc[c+d*x]*(A-C*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  A/a*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  1/a*Int[Sec[c+d*x]*(a*A+A*b-a*B+(A*b-a*C)*Sec[c+d*x])/(a+b*Sec[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  A/a*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  1/a*Int[Csc[c+d*x]*(a*A+A*b-a*B+(A*b-a*C)*Csc[c+d*x])/(a+b*Csc[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  A/a*Int[(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] - 
  1/a*Int[Sec[c+d*x]*(a*A+A*b+(A*b-a*C)*Sec[c+d*x])/(a+b*Sec[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d,A},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  A/a*Int[(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] - 
  1/a*Int[Csc[c+d*x]*(a*A+A*b+(A*b-a*C)*Csc[c+d*x])/(a+b*Csc[c+d*x])^(3/2),x] /;
FreeQ[{a,b,c,d,A},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[A*(a^2-b^2)*(n+1)-a*(b*A-a*B+b*C)*(n+1)*Sec[c+d*x]+(A*b^2-a*b*B+a^2*C)*(n+2)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-3/2


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[A*(a^2-b^2)*(n+1)-a*(b*A-a*B+b*C)*(n+1)*Csc[c+d*x]+(A*b^2-a*b*B+a^2*C)*(n+2)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-3/2


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[A*(a^2-b^2)*(n+1)-a*b*(A+C)*(n+1)*Sec[c+d*x]+(A*b^2+a^2*C)*(n+2)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && IntegerQ[2*n] && n<-1 && n!=-3/2


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[A*(a^2-b^2)*(n+1)-a*b*(A+C)*(n+1)*Csc[c+d*x]+(A*b^2+a^2*C)*(n+2)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && IntegerQ[2*n] && n<-1 && n!=-3/2


(* Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[(a+b*Sec[c+d*x])^n,x] + 
  Int[Sec[c+d*x]*(B+C*Sec[c+d*x])*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[(a+b*Csc[c+d*x])^n,x] + 
  Int[Csc[c+d*x]*(B+C*Csc[c+d*x])*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[(a+b*Sec[c+d*x])^n,x] + 
  C*Int[Sec[c+d*x]^2*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[(a+b*Csc[c+d*x])^n,x] + 
  C*Int[Csc[c+d*x]^2*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[a^2-b^2] *)


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[n]]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[n]]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(A+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[n]]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(A+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[n]]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2)*(b*Sec[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,C,n},x] && IntegerQ[m]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2)*(b*Csc[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,B,C,n},x] && IntegerQ[m]


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+C*Sec[c+d*x]^2)*(b*Sec[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,C,n},x] && IntegerQ[m]


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^m*Int[(A+C*Csc[c+d*x]^2)*(b*Csc[c+d*x])^(m+n),x] /;
FreeQ[{b,c,d,A,C,n},x] && IntegerQ[m]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(b_*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]]*Int[Sec[c+d*x]^(m+n)*(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(b_*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]]*Int[Csc[c+d*x]^(m+n)*(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sec[c_.+d_.*x_]^m_*(A_+C_.*sec[c_.+d_.*x_]^2)*(b_*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]]*Int[Sec[c+d*x]^(m+n)*(A+C*Sec[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[csc[c_.+d_.*x_]^m_*(A_+C_.*csc[c_.+d_.*x_]^2)*(b_*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n-1/2)*Sqrt[b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]]*Int[Csc[c+d*x]^(m+n)*(A+C*Csc[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && PositiveIntegerQ[n+1/2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(b_*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Sec[c+d*x]]/Sqrt[b*Sec[c+d*x]]*Int[Sec[c+d*x]^(m+n)*(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(b_*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Csc[c+d*x]]/Sqrt[b*Csc[c+d*x]]*Int[Csc[c+d*x]^(m+n)*(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sec[c_.+d_.*x_]^m_*(A_+C_.*sec[c_.+d_.*x_]^2)*(b_*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Sec[c+d*x]]/Sqrt[b*Sec[c+d*x]]*Int[Sec[c+d*x]^(m+n)*(A+C*Sec[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[csc[c_.+d_.*x_]^m_*(A_+C_.*csc[c_.+d_.*x_]^2)*(b_*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^(n+1/2)*Sqrt[Csc[c+d*x]]/Sqrt[b*Csc[c+d*x]]*Int[Csc[c+d*x]^(m+n)*(A+C*Csc[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C},x] && Not[IntegerQ[m]] && NegativeIntegerQ[n-1/2]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Sec[c+d*x])^n/Sec[c+d*x]^n*Int[Sec[c+d*x]^(m+n)*(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Csc[c+d*x])^n/Csc[c+d*x]^n*Int[Csc[c+d*x]^(m+n)*(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,B,C,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[sec[c_.+d_.*x_]^m_*(A_+C_.*sec[c_.+d_.*x_]^2)*(b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Sec[c+d*x])^n/Sec[c+d*x]^n*Int[Sec[c+d*x]^(m+n)*(A+C*Sec[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[csc[c_.+d_.*x_]^m_*(A_+C_.*csc[c_.+d_.*x_]^2)*(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Csc[c+d*x])^n/Csc[c+d*x]^n*Int[Csc[c+d*x]^(m+n)*(A+C*Csc[c+d*x]^2),x] /;
FreeQ[{b,c,d,A,C,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n-1/2]]


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -a*A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*m) + 
  1/m*Int[Sec[c+d*x]^(m+1)*Simp[m*(b*A+a*B)+((m+1)*a*A+m*(b*B+a*C))*Sec[c+d*x]+m*b*C*Sec[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && RationalQ[m] && m<-1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  a*A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*m) + 
  1/m*Int[Csc[c+d*x]^(m+1)*Simp[m*(b*A+a*B)+((m+1)*a*A+m*(b*B+a*C))*Csc[c+d*x]+m*b*C*Csc[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && RationalQ[m] && m<-1


Int[sec[c_.+d_.*x_]^m_*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -a*A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(d*m) + 
  1/m*Int[Sec[c+d*x]^(m+1)*Simp[m*b*A+((m+1)*a*A+m*a*C)*Sec[c+d*x]+m*b*C*Sec[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && RationalQ[m] && m<-1


Int[csc[c_.+d_.*x_]^m_*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  a*A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(d*m) + 
  1/m*Int[Csc[c+d*x]^(m+1)*Simp[m*b*A+((m+1)*a*A+m*a*C)*Csc[c+d*x]+m*b*C*Csc[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C},x] && RationalQ[m] && m<-1


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  b*C*Sin[c+d*x]*Sec[c+d*x]^(m+2)/(d*(m+2)) + 
  1/(m+2)*Int[Sec[c+d*x]^m*Simp[(m+2)*a*A+((m+2)*(b*A+a*B)+(m+1)*b*C)*Sec[c+d*x]+(m+2)*(b*B+a*C)*Sec[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -b*C*Cos[c+d*x]*Csc[c+d*x]^(m+2)/(d*(m+2)) + 
  1/(m+2)*Int[Csc[c+d*x]^m*Simp[(m+2)*a*A+((m+2)*(b*A+a*B)+(m+1)*b*C)*Csc[c+d*x]+(m+2)*(b*B+a*C)*Csc[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x]


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  b*C*Sin[c+d*x]*Sec[c+d*x]^(m+2)/(d*(m+2)) + 
  1/(m+2)*Int[Sec[c+d*x]^m*Simp[(m+2)*a*A+((m+2)*b*A+(m+1)*b*C)*Sec[c+d*x]+(m+2)*a*C*Sec[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C,m},x]


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -b*C*Cos[c+d*x]*Csc[c+d*x]^(m+2)/(d*(m+2)) + 
  1/(m+2)*Int[Csc[c+d*x]^m*Simp[(m+2)*a*A+((m+2)*b*A+(m+1)*b*C)*Csc[c+d*x]+(m+2)*a*C*Csc[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,C,m},x]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Sec[c+d*x]*Simp[b*A*(n+2)+b*C*(n+1)+(b*B*(n+2)-a*C)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>-2


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Csc[c+d*x]*Simp[b*A*(n+2)+b*C*(n+1)+(b*B*(n+2)-a*C)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>-2


Int[sec[c_.+d_.*x_]*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Sec[c+d*x]*Simp[b*A*(n+2)+b*C*(n+1)-a*C*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>-2


Int[csc[c_.+d_.*x_]*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Csc[c+d*x]*Simp[b*A*(n+2)+b*C*(n+1)-a*C*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>-2


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(a*b)*Int[Sec[c+d*x]^m*(A*b+a*C*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && ZeroQ[A*b-a*B+b*C]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(a*b)*Int[Csc[c+d*x]^m*(A*b+a*C*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && ZeroQ[A*b-a*B+b*C]


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(a*b)*Int[Sec[c+d*x]^m*(A*b+a*C*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && ZeroQ[A+C]


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  1/(a*b)*Int[Csc[c+d*x]^m*(A*b+a*C*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && ZeroQ[A+C]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b-a*B+b*C)*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*
    Int[Sec[c+d*x]^m*Simp[a*A*(2*n+1)-(b*B-a*A-a*C)*m+(b*C*n-(b*A-a*B)*(n+1)-(A*b-a*B+b*C)*m)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b-a*B+b*C)*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  1/(a^2*(2*n+1))*
    Int[Csc[c+d*x]^m*Simp[a*A*(2*n+1)-(b*B-a*A-a*C)*m+(b*C*n-(b*A-a*B)*(n+1)-(A*b-a*B+b*C)*m)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A+C)*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Sec[c+d*x]^m*Simp[a*A*(2*n+1)+a*(A+C)*m+(b*C*n-b*A*(n+1)-b*(A+C)*m)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A+C)*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[Csc[c+d*x]^m*Simp[a*A*(2*n+1)+a*(A+C)*m+(b*C*n-b*A*(n+1)-b*(A+C)*m)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*m) + 
  1/(a*m)*Int[Sec[c+d*x]^(m+1)*Simp[a*B*m-b*A*n+a*(A*(n+1)+(A+C)*m)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1] && (RationalQ[m] && m<=-1 || ZeroQ[m+n+1])


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*m) + 
  1/(a*m)*Int[Csc[c+d*x]^(m+1)*Simp[a*B*m-b*A*n+a*(A*(n+1)+(A+C)*m)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1] && (RationalQ[m] && m<=-1 || ZeroQ[m+n+1])


Int[sec[c_.+d_.*x_]^m_*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*m) + 
  1/(a*m)*Int[Sec[c+d*x]^(m+1)*Simp[-b*A*n+a*(A*(n+1)+(A+C)*m)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1] && (RationalQ[m] && m<=-1 || ZeroQ[m+n+1])


Int[csc[c_.+d_.*x_]^m_*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*m) + 
  1/(a*m)*Int[Csc[c+d*x]^(m+1)*Simp[-b*A*n+a*(A*(n+1)+(A+C)*m)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1] && (RationalQ[m] && m<=-1 || ZeroQ[m+n+1])


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(m+n+1)) + 
  1/(a*(m+n+1))*Int[Sec[c+d*x]^m*Simp[a*A*(n+1)+a*(A+C)*m+(b*C*n+a*B*(m+n+1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1] && Not[RationalQ[m] && m<=-1 || ZeroQ[m+n+1]]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(m+n+1)) + 
  1/(a*(m+n+1))*Int[Csc[c+d*x]^m*Simp[a*A*(n+1)+a*(A+C)*m+(b*C*n+a*B*(m+n+1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1] && Not[RationalQ[m] && m<=-1 || ZeroQ[m+n+1]]


Int[sec[c_.+d_.*x_]^m_*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(m+n+1)) + 
  1/(a*(m+n+1))*Int[Sec[c+d*x]^m*Simp[a*A*(n+1)+a*(A+C)*m+b*C*n*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1] && Not[RationalQ[m] && m<=-1 || ZeroQ[m+n+1]]


Int[csc[c_.+d_.*x_]^m_*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(m+n+1)) + 
  1/(a*(m+n+1))*Int[Csc[c+d*x]^m*Simp[a*A*(n+1)+a*(A+C)*m+b*C*n*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[n] && n<=-1] && Not[RationalQ[m] && m<=-1 || ZeroQ[m+n+1]]


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]*Simp[b*(a*A-b*B+a*C)*(n+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(n+1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]*Simp[b*(a*A-b*B+a*C)*(n+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(n+1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[sec[c_.+d_.*x_]*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]*Simp[a*b*(A+C)*(n+1)-(A*b^2+a^2*C+b^2*(A+C)*(n+1))*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[csc[c_.+d_.*x_]*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]*Simp[a*b*(A+C)*(n+1)-(A*b^2+a^2*C+b^2*(A+C)*(n+1))*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1


Int[sec[c_.+d_.*x_]*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Sec[c+d*x]*Simp[b*A*(n+2)+b*C*(n+1)+(b*B*(n+2)-a*C)*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[n] && n<-1]


Int[csc[c_.+d_.*x_]*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Csc[c+d*x]*Simp[b*A*(n+2)+b*C*(n+1)+(b*B*(n+2)-a*C)*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[n] && n<-1]


Int[sec[c_.+d_.*x_]*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Sec[c+d*x]*Simp[b*A*(n+2)+b*C*(n+1)-a*C*Sec[c+d*x],x]*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[n] && n<-1]


Int[csc[c_.+d_.*x_]*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+2)) + 
  1/(b*(n+2))*Int[Csc[c+d*x]*Simp[b*A*(n+2)+b*C*(n+1)-a*C*Csc[c+d*x],x]*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,n},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[n] && n<-1]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*m) + 
  1/m*
    Int[Sec[c+d*x]^(m+1)*
      Simp[a*B*m-b*A*n+(a*A+(a*A+a*C+b*B)*m)*Sec[c+d*x]+b*(A*(n+1)+(A+C)*m)*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>0 && m<=-1


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*m) + 
  1/m*
    Int[Csc[c+d*x]^(m+1)*
      Simp[a*B*m-b*A*n+(a*A+(a*A+a*C+b*B)*m)*Csc[c+d*x]+b*(A*(n+1)+(A+C)*m)*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>0 && m<=-1


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*m) + 
  1/m*Int[Sec[c+d*x]^(m+1)*Simp[-b*A*n+a*(A+(A+C)*m)*Sec[c+d*x]+b*(A*(n+1)+(A+C)*m)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>0 && m<=-1


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*m) + 
  1/m*Int[Csc[c+d*x]^(m+1)*Simp[-b*A*n+a*(A+(A+C)*m)*Csc[c+d*x]+b*(A*(n+1)+(A+C)*m)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n>0 && m<=-1


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(m+n+1)) + 
  1/(m+n+1)*
    Int[Sec[c+d*x]^m*
      Simp[a*(A*(n+1)+(A+C)*m)+(b*A+a*B+(b*A+a*B+b*C)*(m+n))*Sec[c+d*x]+(a*C*n+b*B*(m+n+1))*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<=-1]


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(m+n+1)) + 
  1/(m+n+1)*
    Int[Csc[c+d*x]^m*
      Simp[a*(A*(n+1)+(A+C)*m)+(b*A+a*B+(b*A+a*B+b*C)*(m+n))*Csc[c+d*x]+(a*C*n+b*B*(m+n+1))*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<=-1]


Int[sec[c_.+d_.*x_]^m_*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  C*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^n/(d*(m+n+1)) + 
  1/(m+n+1)*
    Int[Sec[c+d*x]^m*
      Simp[a*(A*(n+1)+(A+C)*m)+(b*A+(b*A+b*C)*(m+n))*Sec[c+d*x]+a*C*n*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<=-1]


Int[csc[c_.+d_.*x_]^m_*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^n/(d*(m+n+1)) + 
  1/(m+n+1)*
    Int[Csc[c+d*x]^m*
      Simp[a*(A*(n+1)+(A+C)*m)+(b*A+(b*A+b*C)*(m+n))*Csc[c+d*x]+a*C*n*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<=-1]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  (b*B-a*C)/b^2*Int[Sec[c+d*x]^m,x] + C/b*Int[Sec[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  (b*B-a*C)/b^2*Int[Csc[c+d*x]^m,x] + C/b*Int[Csc[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -a*C/b^2*Int[Sec[c+d*x]^m,x] + C/b*Int[Sec[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[A*b^2+a^2*C]


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -a*C/b^2*Int[Csc[c+d*x]^m,x] + C/b*Int[Csc[c+d*x]^(m+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && ZeroQ[A*b^2+a^2*C]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  C*Sin[c+d*x]*Sec[c+d*x]^m/(b*d*m) + 
  1/(b*m)*Int[Sec[c+d*x]^(m-1)*Simp[a*C*(m-1)+b*(A+(A+C)*(m-1))*Sec[c+d*x]+m*(b*B-a*C)*Sec[c+d*x]^2,x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -C*Cos[c+d*x]*Csc[c+d*x]^m/(b*d*m) + 
  1/(b*m)*Int[Csc[c+d*x]^(m-1)*Simp[a*C*(m-1)+b*(A+(A+C)*(m-1))*Csc[c+d*x]+m*(b*B-a*C)*Csc[c+d*x]^2,x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  C*Sin[c+d*x]*Sec[c+d*x]^m/(b*d*m) + 
  1/(b*m)*Int[Sec[c+d*x]^(m-1)*Simp[a*C*(m-1)+b*(A+(A+C)*(m-1))*Sec[c+d*x]-a*C*m*Sec[c+d*x]^2,x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -C*Cos[c+d*x]*Csc[c+d*x]^m/(b*d*m) + 
  1/(b*m)*Int[Csc[c+d*x]^(m-1)*Simp[a*C*(m-1)+b*(A+(A+C)*(m-1))*Csc[c+d*x]-a*C*m*Csc[c+d*x]^2,x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[sec[c_.+d_.*x_]^m_*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(a*d*m) + 
  1/(a*m)*Int[Sec[c+d*x]^(m+1)*Simp[(a*B-b*A)*m+a*(A+(A+C)*m)*Sec[c+d*x]+b*A*(m+1)*Sec[c+d*x]^2,x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<=-1


Int[csc[c_.+d_.*x_]^m_*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(a*d*m) + 
  1/(a*m)*Int[Csc[c+d*x]^(m+1)*Simp[(a*B-b*A)*m+a*(A+(A+C)*m)*Csc[c+d*x]+b*A*(m+1)*Csc[c+d*x]^2,x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<=-1


Int[sec[c_.+d_.*x_]^m_*(A_+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)/(a*d*m) + 
  1/(a*m)*Int[Sec[c+d*x]^(m+1)*Simp[-b*A*m+a*(A+(A+C)*m)*Sec[c+d*x]+b*A*(m+1)*Sec[c+d*x]^2,x]/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<=-1


Int[csc[c_.+d_.*x_]^m_*(A_+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)/(a*d*m) + 
  1/(a*m)*Int[Csc[c+d*x]^(m+1)*Simp[-b*A*m+a*(A+(A+C)*m)*Csc[c+d*x]+b*A*(m+1)*Csc[c+d*x]^2,x]/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<=-1


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  Sec[c+d*x]^m*Cos[c+d*x]^m*Int[(C+B*Cos[c+d*x]+A*Cos[c+d*x]^2)/(Cos[c+d*x]^(m+1)*(b+a*Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  Csc[c+d*x]^m*Sin[c+d*x]^m*Int[(C+B*Sin[c+d*x]+A*Sin[c+d*x]^2)/(Sin[c+d*x]^(m+1)*(b+a*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  Sec[c+d*x]^m*Cos[c+d*x]^m*Int[(C+A*Cos[c+d*x]^2)/(Cos[c+d*x]^(m+1)*(b+a*Cos[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2]


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  Csc[c+d*x]^m*Sin[c+d*x]^m*Int[(C+A*Sin[c+d*x]^2)/(Sin[c+d*x]^(m+1)*(b+a*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*C*Sin[c+d*x]*Sec[c+d*x]^m*Sqrt[a+b*Sec[c+d*x]]/(b*d*(2*m+1)) + 
  1/(b*(2*m+1))*
    Int[Sec[c+d*x]^(m-1)*Simp[2*a*C*(m-1)+b*(2*A+(A+C)*(2*m-1))*Sec[c+d*x]+(b*B+2*m*(b*B-a*C))*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*C*Cos[c+d*x]*Csc[c+d*x]^m*Sqrt[a+b*Csc[c+d*x]]/(b*d*(2*m+1)) + 
  1/(b*(2*m+1))*
    Int[Csc[c+d*x]^(m-1)*Simp[2*a*C*(m-1)+b*(2*A+(A+C)*(2*m-1))*Csc[c+d*x]+(b*B+2*m*(b*B-a*C))*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*C*Sin[c+d*x]*Sec[c+d*x]^m*Sqrt[a+b*Sec[c+d*x]]/(b*d*(2*m+1)) + 
  1/(b*(2*m+1))*
    Int[Sec[c+d*x]^(m-1)*Simp[2*a*C*(m-1)+b*(2*A+(A+C)*(2*m-1))*Sec[c+d*x]-2*a*C*m*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*C*Cos[c+d*x]*Csc[c+d*x]^m*Sqrt[a+b*Csc[c+d*x]]/(b*d*(2*m+1)) + 
  1/(b*(2*m+1))*
    Int[Csc[c+d*x]^(m-1)*Simp[2*a*C*(m-1)+b*(2*A+(A+C)*(2*m-1))*Csc[c+d*x]-2*a*C*m*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(sec[c_.+d_.*x_]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  A*Sin[c+d*x]*Sqrt[a+b*Sec[c+d*x]]/(a*d*(1+Sec[c+d*x])) + 
  A/a*Int[Sqrt[a+b*Sec[c+d*x]]/(1+Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && ZeroQ[B-C] && ZeroQ[A*b-2*a*B]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(csc[c_.+d_.*x_]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  -A*Cos[c+d*x]*Sqrt[a+b*Csc[c+d*x]]/(a*d*(1+Csc[c+d*x])) + 
  A/a*Int[Sqrt[a+b*Csc[c+d*x]]/(1+Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && ZeroQ[B-C] && ZeroQ[A*b-2*a*B]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(sec[c_.+d_.*x_]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  -1/(2*a)*Int[(A*b-2*a*B+(A*b-2*a*C)*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] + 
  A/(2*a)*Int[(2*a+b*Sec[c+d*x]+b*Sec[c+d*x]^2)/(Sec[c+d*x]*Sqrt[a+b*Sec[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && Not[ZeroQ[B-C] && ZeroQ[A*b-2*a*B]]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(csc[c_.+d_.*x_]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  -1/(2*a)*Int[(A*b-2*a*B+(A*b-2*a*C)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  A/(2*a)*Int[(2*a+b*Csc[c+d*x]+b*Csc[c+d*x]^2)/(Csc[c+d*x]*Sqrt[a+b*Csc[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && Not[ZeroQ[B-C] && ZeroQ[A*b-2*a*B]]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)/(sec[c_.+d_.*x_]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  -1/(2*a)*Int[(A*b+(A*b-2*a*C)*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] + 
  A/(2*a)*Int[(2*a+b*Sec[c+d*x]+b*Sec[c+d*x]^2)/(Sec[c+d*x]*Sqrt[a+b*Sec[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)/(csc[c_.+d_.*x_]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  -1/(2*a)*Int[(A*b+(A*b-2*a*C)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  A/(2*a)*Int[(2*a+b*Csc[c+d*x]+b*Csc[c+d*x]^2)/(Csc[c+d*x]*Sqrt[a+b*Csc[c+d*x]]),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/(Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]],x] - 
  1/a*Int[Sqrt[Sec[c+d*x]]*(A*b-a*B-a*C*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/(Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]],x] - 
  1/a*Int[Sqrt[Csc[c+d*x]]*(A*b-a*B-a*C*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sec[c_.+d_.*x_]^2)/(Sqrt[sec[c_.+d_.*x_]]*Sqrt[a_+b_.*sec[c_.+d_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Sec[c+d*x]]/Sqrt[Sec[c+d*x]],x] - 
  1/a*Int[Sqrt[Sec[c+d*x]]*(A*b-a*C*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*csc[c_.+d_.*x_]^2)/(Sqrt[csc[c_.+d_.*x_]]*Sqrt[a_+b_.*csc[c_.+d_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Csc[c+d*x]]/Sqrt[Csc[c+d*x]],x] - 
  1/a*Int[Sqrt[Csc[c+d*x]]*(A*b-a*C*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]]/(a*d*m) + 
  1/(2*a*m)*Int[Sec[c+d*x]^(m+1)*Simp[2*m*(a*B-b*A)-b*A+2*a*(A+m*(A+C))*Sec[c+d*x]+b*A*(2*m+3)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]]/(a*d*m) + 
  1/(2*a*m)*Int[Csc[c+d*x]^(m+1)*Simp[2*m*(a*B-b*A)-b*A+2*a*(A+m*(A+C))*Csc[c+d*x]+b*A*(2*m+3)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  -A*Sin[c+d*x]*Sec[c+d*x]^(m+1)*Sqrt[a+b*Sec[c+d*x]]/(a*d*m) + 
  1/(2*a*m)*Int[Sec[c+d*x]^(m+1)*Simp[-2*b*A*m-b*A+2*a*(A+m*(A+C))*Sec[c+d*x]+b*A*(2*m+3)*Sec[c+d*x]^2,x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  A*Cos[c+d*x]*Csc[c+d*x]^(m+1)*Sqrt[a+b*Csc[c+d*x]]/(a*d*m) + 
  1/(2*a*m)*Int[Csc[c+d*x]^(m+1)*Simp[-2*b*A*m-b*A+2*a*(A+m*(A+C))*Csc[c+d*x]+b*A*(2*m+3)*Csc[c+d*x]^2,x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[Sec[c+d*x]^m*(b*B-a*C+b*C*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[Csc[c+d*x]^m*(b*B-a*C+b*C*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -C/b^2*Int[Sec[c+d*x]^m*(a-b*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && ZeroQ[A*b^2+a^2*C]


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -C/b^2*Int[Csc[c+d*x]^m*(a-b*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && ZeroQ[A*b^2+a^2*C]


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Sin[c+d*x]*Sec[c+d*x]^m*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]^(m-1)*
      Simp[(A*b^2-a*b*B+a^2*C)*(m-1)+b*(a*A-b*B+a*C)*(n+1)*Sec[c+d*x]-((b^2*A-a*b*B+b^2*C)*(n+1)+(A*b^2-a*b*B+a^2*C)*m)*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>0


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cos[c+d*x]*Csc[c+d*x]^m*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]^(m-1)*
      Simp[(A*b^2-a*b*B+a^2*C)*(m-1)+b*(a*A-b*B+a*C)*(n+1)*Csc[c+d*x]-((b^2*A-a*b*B+b^2*C)*(n+1)+(A*b^2-a*b*B+a^2*C)*m)*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>0


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Sin[c+d*x]*Sec[c+d*x]^m*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]^(m-1)*
      Simp[(A*b^2+a^2*C)*(m-1)+b*(a*A+a*C)*(n+1)*Sec[c+d*x]-((b^2*A+b^2*C)*(n+1)+(A*b^2+a^2*C)*m)*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>0


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Cos[c+d*x]*Csc[c+d*x]^m*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  1/(b*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]^(m-1)*
      Simp[(A*b^2+a^2*C)*(m-1)+b*(a*A+a*C)*(n+1)*Csc[c+d*x]-((b^2*A+b^2*C)*(n+1)+(A*b^2+a^2*C)*m)*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && n<-1 && m>0


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-(A*b^2-a*b*B+a^2*C)*m-a*(b*A-a*B+b*C)*(n+1)*Sec[c+d*x]+(A*b^2-a*b*B+a^2*C)*(m+n+2)*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>0]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-(A*b^2-a*b*B+a^2*C)*m-a*(b*A-a*B+b*C)*(n+1)*Csc[c+d*x]+(A*b^2-a*b*B+a^2*C)*(m+n+2)*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>0]


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -(A*b^2+a^2*C)*Sin[c+d*x]*Sec[c+d*x]^(m+1)*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Sec[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-(A*b^2+a^2*C)*m-a*b*(A+C)*(n+1)*Sec[c+d*x]+(A*b^2+a^2*C)*(m+n+2)*Sec[c+d*x]^2,x]*
      (a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>0]


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (A*b^2+a^2*C)*Cos[c+d*x]*Csc[c+d*x]^(m+1)*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Csc[c+d*x]^m*
      Simp[A*(a^2-b^2)*(n+1)-(A*b^2+a^2*C)*m-a*b*(A+C)*(n+1)*Csc[c+d*x]+(A*b^2+a^2*C)*(m+n+2)*Csc[c+d*x]^2,x]*
      (a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && Not[RationalQ[m] && m>0]


(* Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Sec[c+d*x]^m*(a+b*Sec[c+d*x])^n,x] + 
  Int[Sec[c+d*x]^(m+1)*(B+C*Sec[c+d*x])*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Csc[c+d*x]^m*(a+b*Csc[c+d*x])^n,x] + 
  Int[Csc[c+d*x]^(m+1)*(B+C*Csc[c+d*x])*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Sec[c+d*x]^m*(a+b*Sec[c+d*x])^n,x] + 
  C*Int[Sec[c+d*x]^(m+2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && NonzeroQ[a^2-b^2] *)


(* Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  A*Int[Csc[c+d*x]^m*(a+b*Csc[c+d*x])^n,x] + 
  C*Int[Csc[c+d*x]^(m+2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x] && NonzeroQ[a^2-b^2] *)


Int[sec[c_.+d_.*x_]^m_.*(A_+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][Sec[c+d*x]^m*(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x]


Int[csc[c_.+d_.*x_]^m_.*(A_+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][Csc[c+d*x]^m*(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,B,C,m,n},x]


Int[sec[c_.+d_.*x_]^m_.*(A_+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][Sec[c+d*x]^m*(A+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x]


Int[csc[c_.+d_.*x_]^m_.*(A_+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][Csc[c+d*x]^m*(A+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,A,C,m,n},x]


Int[(e_.*cos[c_.+d_.*x_])^m_*(A_.+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2),x_Symbol] :=
  e^2*Int[(e*Cos[c+d*x])^(m-2)*(C+B*Cos[c+d*x]+A*Cos[c+d*x]^2),x] /;
FreeQ[{c,d,e,A,B,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*sin[c_.+d_.*x_])^m_*(A_.+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2),x_Symbol] :=
  e^2*Int[(e*Sin[c+d*x])^(m-2)*(C+B*Sin[c+d*x]+A*Sin[c+d*x]^2),x] /;
FreeQ[{c,d,e,A,B,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_*(A_.+C_.*sec[c_.+d_.*x_]^2),x_Symbol] :=
  e^2*Int[(e*Cos[c+d*x])^(m-2)*(C+A*Cos[c+d*x]^2),x] /;
FreeQ[{c,d,e,A,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*sin[c_.+d_.*x_])^m_*(A_.+C_.*csc[c_.+d_.*x_]^2),x_Symbol] :=
  e^2*Int[(e*Sin[c+d*x])^(m-2)*(C+A*Sin[c+d*x]^2),x] /;
FreeQ[{c,d,e,A,C,m},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_.*(f_.*sec[c_.+d_.*x_])^p_.*(A_.+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Cos[c+d*x])^m*(f*Sec[c+d*x])^p/Sec[c+d*x]^(p-m)*Int[Sec[c+d*x]^(p-m)*(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,B,C,m,p},x]


Int[(e_.*sin[c_.+d_.*x_])^m_.*(f_.*csc[c_.+d_.*x_])^p_.*(A_.+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Sin[c+d*x])^m*(f*Csc[c+d*x])^p/Csc[c+d*x]^(p-m)*Int[Csc[c+d*x]^(p-m)*(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,B,C,m,p},x]


Int[(e_.*cos[c_.+d_.*x_])^m_.*(f_.*sec[c_.+d_.*x_])^p_.*(A_.+C_.*sec[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Cos[c+d*x])^m*(f*Sec[c+d*x])^p/Sec[c+d*x]^(p-m)*Int[Sec[c+d*x]^(p-m)*(A+C*Sec[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,C,m,p},x]


Int[(e_.*sin[c_.+d_.*x_])^m_.*(f_.*csc[c_.+d_.*x_])^p_.*(A_.+C_.*csc[c_.+d_.*x_]^2),x_Symbol] :=
  (e*Sin[c+d*x])^m*(f*Csc[c+d*x])^p/Csc[c+d*x]^(p-m)*Int[Csc[c+d*x]^(p-m)*(A+C*Csc[c+d*x]^2),x] /;
FreeQ[{c,d,e,f,A,C,m,p},x]


Int[(e_*sec[c_.+d_.*x_])^m_*(A_.+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m/Sec[c+d*x]^m*Int[Sec[c+d*x]^m*(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*csc[c_.+d_.*x_])^m_*(A_.+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m/Csc[c+d*x]^m*Int[Csc[c+d*x]^m*(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*sec[c_.+d_.*x_])^m_*(A_.+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sec[c+d*x])^m/Sec[c+d*x]^m*Int[Sec[c+d*x]^m*(A+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_*csc[c_.+d_.*x_])^m_*(A_.+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Csc[c+d*x])^m/Csc[c+d*x]^m*Int[Csc[c+d*x]^m*(A+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_*(A_.+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m*Sec[c+d*x]^m*Int[(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n/Sec[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*sin[c_.+d_.*x_])^m_*(A_.+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m*Csc[c+d*x]^m*Int[(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n/Csc[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,B,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_*(A_.+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m*Sec[c+d*x]^m*Int[(A+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n/Sec[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*sin[c_.+d_.*x_])^m_*(A_.+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m*Csc[c+d*x]^m*Int[(A+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n/Csc[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,A,C,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*cos[c_.+d_.*x_])^m_.*(f_.*sec[c_.+d_.*x_])^p_.*(A_.+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m*(f*Sec[c+d*x])^p/Sec[c+d*x]^(p-m)*Int[Sec[c+d*x]^(p-m)*(A+B*Sec[c+d*x]+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x]


Int[(e_.*sin[c_.+d_.*x_])^m_.*(f_.*csc[c_.+d_.*x_])^p_.*(A_.+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m*(f*Csc[c+d*x])^p/Csc[c+d*x]^(p-m)*Int[Csc[c+d*x]^(p-m)*(A+B*Csc[c+d*x]+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x]


Int[(e_.*cos[c_.+d_.*x_])^m_.*(f_.*sec[c_.+d_.*x_])^p_.*(A_.+C_.*sec[c_.+d_.*x_]^2)*(a_.+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cos[c+d*x])^m*(f*Sec[c+d*x])^p/Sec[c+d*x]^(p-m)*Int[Sec[c+d*x]^(p-m)*(A+C*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n,p},x]


Int[(e_.*sin[c_.+d_.*x_])^m_.*(f_.*csc[c_.+d_.*x_])^p_.*(A_.+C_.*csc[c_.+d_.*x_]^2)*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Sin[c+d*x])^m*(f*Csc[c+d*x])^p/Csc[c+d*x]^(p-m)*Int[Csc[c+d*x]^(p-m)*(A+C*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n,p},x]


Int[u_.*(A_+B_.*cos[c_.+d_.*x_]+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Sec[c+d*x]+A*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n/Sec[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x]


Int[u_.*(A_+B_.*sin[c_.+d_.*x_]+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Csc[c+d*x]+A*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n/Csc[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,B,C,n},x]


Int[u_.*(A_+C_.*cos[c_.+d_.*x_]^2)*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Sec[c+d*x]^2)*(a+b*Sec[c+d*x])^n/Sec[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,C,n},x]


Int[u_.*(A_+C_.*sin[c_.+d_.*x_]^2)*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n/Csc[c+d*x]^2,x] /;
FreeQ[{a,b,c,d,A,C,n},x]


(* ::Subsection::Closed:: *)
(*7.3.4 trig(c+d x)^m (a+b sec(c+d x))^n*)


(* Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  -1/d*Subst[Int[(1-x^2)^((m-1)/2)*(b+a*x)^n/x^n,x],x,Cos[c+d*x]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && IntegerQ[n] *)


(* Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(1-x^2)^((m-1)/2)*(b+a*x)^n/x^n,x],x,Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && IntegerQ[n] *)


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  Sin[c+d*x]^(m-1)/(b*d*(m-1)) - 1/a*Int[Cos[c+d*x]^2*Sin[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m-1]


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]^(m-1)/(b*d*(m-1)) - 1/a*Int[Sin[c+d*x]^2*Cos[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m-1]


Int[sin[c_.+d_.*x_]^m_./(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -1/d*Subst[Int[x*(1-x^2)^((m-1)/2)/(b+a*x),x],x,Cos[c+d*x]] /;
FreeQ[{a,b,c,d},x] (* && NonzeroQ[a^2-b^2] *) && OddQ[m]


Int[cos[c_.+d_.*x_]^m_./(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  1/d*Subst[Int[x*(1-x^2)^((m-1)/2)/(b+a*x),x],x,Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] (* && NonzeroQ[a^2-b^2] *) && OddQ[m]


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  b*Sin[c+d*x]^(m-1)/(d*a^2*(m-1)) - 
  1/a*Int[Cos[c+d*x]^2*Sin[c+d*x]^(m-2),x] + 
  (a^2-b^2)/a^2*Int[Sin[c+d*x]^(m-2)/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m>1


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -b*Cos[c+d*x]^(m-1)/(d*a^2*(m-1)) - 
  1/a*Int[Sin[c+d*x]^2*Cos[c+d*x]^(m-2),x] + 
  (a^2-b^2)/a^2*Int[Cos[c+d*x]^(m-2)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m>1


Int[sin[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -b*Sin[c+d*x]^(m+1)/(d*(m+1)*(a^2-b^2)) + 
  a/(a^2-b^2)*Int[Cos[c+d*x]^2*Sin[c+d*x]^m,x] + 
  a^2/(a^2-b^2)*Int[Sin[c+d*x]^(m+2)/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m<-1


Int[cos[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  b*Cos[c+d*x]^(m+1)/(d*(m+1)*(a^2-b^2)) + 
  a/(a^2-b^2)*Int[Sin[c+d*x]^2*Cos[c+d*x]^m,x] + 
  a^2/(a^2-b^2)*Int[Cos[c+d*x]^(m+2)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^2*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(1-Cos[c+d*x]^2)*(b+a*Cos[c+d*x])^n/Cos[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n]


Int[cos[c_.+d_.*x_]^2*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(1-Sin[c+d*x]^2)*(b+a*Sin[c+d*x])^n/Sin[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n]


Int[sin[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(1-Cos[c+d*x]^2)^(m/2)*(b+a*Cos[c+d*x])^n/Cos[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && EvenQ[m]


Int[cos[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(1-Sin[c+d*x]^2)^(m/2)*(b+a*Sin[c+d*x])^n/Sin[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && EvenQ[m]


Int[tan[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -1/a*Int[Tan[c+d*x]^(m-2),x] + 1/b*Int[Sec[c+d*x]*Tan[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m-1]


Int[cot[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -1/a*Int[Cot[c+d*x]^(m-2),x] + 1/b*Int[Csc[c+d*x]*Cot[c+d*x]^(m-2),x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m-1]


Int[tan[c_.+d_.*x_]^m_./(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -1/d*Subst[Int[(1-x^2)^((m-1)/2)/(x^(m-1)*(b+a*x)),x],x,Cos[c+d*x]] /;
FreeQ[{a,b,c,d},x] (* && NonzeroQ[a^2-b^2] *) && OddQ[m]


Int[cot[c_.+d_.*x_]^m_./(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  1/d*Subst[Int[(1-x^2)^((m-1)/2)/(x^(m-1)*(b+a*x)),x],x,Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] (* && NonzeroQ[a^2-b^2] *) && OddQ[m]


Int[tan[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -a/b^2*Int[Tan[c+d*x]^(m-2),x] + 
  1/b*Int[Sec[c+d*x]*Tan[c+d*x]^(m-2),x] + 
  (a^2-b^2)/b^2*Int[Tan[c+d*x]^(m-2)/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m>1


Int[cot[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -a/b^2*Int[Cot[c+d*x]^(m-2),x] + 
  1/b*Int[Csc[c+d*x]*Cot[c+d*x]^(m-2),x] + 
  (a^2-b^2)/b^2*Int[Cot[c+d*x]^(m-2)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m>1


Int[tan[c_.+d_.*x_]^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  a/(a^2-b^2)*Int[Tan[c+d*x]^m,x] - 
  b/(a^2-b^2)*Int[Sec[c+d*x]*Tan[c+d*x]^m,x] + 
  b^2/(a^2-b^2)*Int[Tan[c+d*x]^(m+2)/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m<-1


Int[cot[c_.+d_.*x_]^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  a/(a^2-b^2)*Int[Cot[c+d*x]^m,x] - 
  b/(a^2-b^2)*Int[Csc[c+d*x]*Cot[c+d*x]^m,x] + 
  b^2/(a^2-b^2)*Int[Cot[c+d*x]^(m+2)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m<-1


Int[sin[c_.+d_.*x_]^2*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(1-Cos[c+d*x]^2)*(b+a*Cos[c+d*x])^n/Cos[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n]


Int[cos[c_.+d_.*x_]^2*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(1-Sin[c+d*x]^2)*(b+a*Sin[c+d*x])^n/Sin[c+d*x]^n,x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n]


Int[tan[c_.+d_.*x_]^m_*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(1-Cos[c+d*x]^2)^(m/2)*(b+a*Cos[c+d*x])^n/Cos[c+d*x]^(m+n),x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && EvenQ[m]


Int[cot[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(1-Sin[c+d*x]^2)^(m/2)*(b+a*Sin[c+d*x])^n/Sin[c+d*x]^(m+n),x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && EvenQ[m]


(* ::Subsection::Closed:: *)
(*8.1 trig(c+d x)^m (a cos(c+d x)+b sin(c+d x))^n*)


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
(*8.2 (a+b cos(c+d x)+c sin(c+d x))^n*)


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
  Log[RemoveContent[b^2+c^2+(a*b-c*Rt[-a^2+b^2+c^2,2])*Cos[d+e*x]+(a*c+b*Sqrt[-a^2+b^2+c^2])*Sin[d+e*x],x]]/(2*e*Rt[-a^2+b^2+c^2,2]) - 
  Log[RemoveContent[b^2+c^2+(a*b+c*Rt[-a^2+b^2+c^2,2])*Cos[d+e*x]+(a*c-b*Sqrt[-a^2+b^2+c^2])*Sin[d+e*x],x]]/(2*e*Rt[-a^2+b^2+c^2,2]) /;
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
	Simp[a*(b*B+c*C)*n+a^2*A*(n+1)+(n*(a^2*B-B*c^2+b*c*C)+a*b*A*(n+1))*Cos[d+e*x]+(n*(b*B*c+a^2*C-b^2*C)+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
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
(*8.3 Inert Trig Functions Rules*)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  Module[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[1,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && (F===Cos || F===cos)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  Module[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[1,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && (F===Sin || F===sin)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  Module[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  1/(b*c)*Subst[Int[SubstFor[1/x,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && (F===Cot || F===cot)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  Module[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -1/(b*c)*Subst[Int[SubstFor[1/x,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && (F===Tan || F===tan)


Int[u_*F_[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
  Module[{d=FreeFactors[Tan[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[1,Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
 FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && NonsumQ[u] && (F===Sec || F===sec)


Int[u_/cos[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
  Module[{d=FreeFactors[Tan[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[1,Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
 FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && NonsumQ[u]


Int[u_*F_[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
  Module[{d=FreeFactors[Cot[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[1,Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
 FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && NonsumQ[u] && (F===Csc || F===csc)


Int[u_/sin[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
  Module[{d=FreeFactors[Cot[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[1,Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
 FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && NonsumQ[u]


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
  Module[{d=FreeFactors[Tan[c*(a+b*x)],x]},
  1/(b*c*d^(n-1))*Subst[Int[SubstFor[1/(x^n*(1+d^2*x^2)),Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
 FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True] && TryPureTanSubst[ActivateTrig[u]*Cot[c*(a+b*x)]^n,x]] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && (F===Cot || F===cot)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
  Module[{d=FreeFactors[Cot[c*(a+b*x)],x]},
  -1/(b*c*d^(n-1))*Subst[Int[SubstFor[1/(x^n*(1+d^2*x^2)),Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
 FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True] && TryPureTanSubst[ActivateTrig[u]*Tan[c*(a+b*x)]^n,x]] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && (F===Tan || F===tan)


If[ShowSteps,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Cot[a+b*x]],x]","-1/b*Subst[Int[F[x]/(1+x^2),x],x,Cot[a+b*x]]",Hold[
  Module[{d=FreeFactors[Cot[v],x]},
  Dist[-d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Cot[v]/d,u,x],x],x,Cot[v]/d],x]]]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Cot[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]] /;
SimplifyFlag,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  Module[{d=FreeFactors[Cot[v],x]},
  Dist[-d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Cot[v]/d,u,x],x],x,Cot[v]/d],x]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Cot[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]]]


If[ShowSteps,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Tan[a+b*x]],x]","1/b*Subst[Int[F[x]/(1+x^2),x],x,Tan[a+b*x]]",Hold[
  Module[{d=FreeFactors[Tan[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d],x]]]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]] /;
SimplifyFlag,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  Module[{d=FreeFactors[Tan[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d],x]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]]]


Int[F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[ActivateTrig[F[a+b*x]^p*G[c+d*x]^q],x],x] /;
FreeQ[{a,b,c,d},x] && (F===sin || F===cos) && (G===sin || G===cos) && PositiveIntegerQ[p,q]


Int[F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.*H_[e_.+f_.*x_]^r_.,x_Symbol] :=
  Int[ExpandTrigReduce[ActivateTrig[F[a+b*x]^p*G[c+d*x]^q*H[e+f*x]^r],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && (F===sin || F===cos) && (G===sin || G===cos) && (H===sin || H===cos) && PositiveIntegerQ[p,q,r]


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  Module[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[1,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && (F===Cos || F===cos)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  Module[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[1,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && (F===Sin || F===sin)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  Module[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  1/(b*c)*Subst[Int[SubstFor[1/x,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && (F===Cot || F===cot)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  Module[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -1/(b*c)*Subst[Int[SubstFor[1/x,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && (F===Tan || F===tan)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  Module[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2),Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Cos || F===cos)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  Module[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[(1-d^2*x^2)^((-n-1)/2),Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Sec || F===sec)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  Module[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2),Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Sin || F===sin)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  Module[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[(1-d^2*x^2)^((-n-1)/2),Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Csc || F===csc)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  Module[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  1/(b*c*d^(n-1))*Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2)/x^n,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Cot || F===cot)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  Module[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -1/(b*c*d^(n-1))*Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2)/x^n,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Tan || F===tan)


Int[u_*(v_+d_.*F_[c_.*(a_.+b_.*x_)]^n_.),x_Symbol] :=
  Module[{e=FreeFactors[Sin[c*(a+b*x)],x]},
  Int[ActivateTrig[u*v],x] + d*Int[ActivateTrig[u]*Cos[c*(a+b*x)]^n,x] /;
 FunctionOfQ[Sin[c*(a+b*x)]/e,u,x]] /;
FreeQ[{a,b,c,d},x] && Not[FreeQ[v,x]] && OddQ[n] && NonsumQ[u] && (F===Cos || F===cos)


Int[u_*(v_+d_.*F_[c_.*(a_.+b_.*x_)]^n_.),x_Symbol] :=
  Module[{e=FreeFactors[Cos[c*(a+b*x)],x]},
  Int[ActivateTrig[u*v],x] + d*Int[ActivateTrig[u]*Sin[c*(a+b*x)]^n,x] /;
 FunctionOfQ[Cos[c*(a+b*x)]/e,u,x]] /;
FreeQ[{a,b,c,d},x] && Not[FreeQ[v,x]] && OddQ[n] && NonsumQ[u] && (F===Sin || F===sin)


If[ShowSteps,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Sin[a+b*x]]*Cos[a+b*x],x]","Subst[Int[F[x],x],x,Sin[a+b*x]]/b",Hold[
  Module[{d=FreeFactors[Sin[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1,Sin[v]/d,u/Cos[v],x],x],x,Sin[v]/d],x]]]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Sin[v],x],u/Cos[v],x]] /;
SimplifyFlag,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  Module[{d=FreeFactors[Sin[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1,Sin[v]/d,u/Cos[v],x],x],x,Sin[v]/d],x]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Sin[v],x],u/Cos[v],x]]]


If[ShowSteps,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Cos[a+b*x]]*Sin[a+b*x],x]","-Subst[Int[F[x],x],x,Cos[a+b*x]]/b",Hold[
  Module[{d=FreeFactors[Cos[v],x]},
  Dist[-d/Coefficient[v,x,1],Subst[Int[SubstFor[1,Cos[v]/d,u/Sin[v],x],x],x,Cos[v]/d],x]]]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Cos[v],x],u/Sin[v],x]] /;
SimplifyFlag,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  Module[{d=FreeFactors[Cos[v],x]},
  Dist[-d/Coefficient[v,x,1],Subst[Int[SubstFor[1,Cos[v]/d,u/Sin[v],x],x],x,Cos[v]/d],x]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Cos[v],x],u/Sin[v],x]]]


Int[u_.*(a_.+b_.*cos[d_.+e_.*x_]^2+c_.*sin[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
  (a+c)^p*Int[ActivateTrig[u],x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b-c]


Int[u_.*(a_.+b_.*tan[d_.+e_.*x_]^2+c_.*sec[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
  (a+c)^p*Int[ActivateTrig[u],x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b+c]


Int[u_.*(a_.+b_.*cot[d_.+e_.*x_]^2+c_.*csc[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
  (a+c)^p*Int[ActivateTrig[u],x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b+c]


Int[u_/y_,x_Symbol] :=
  Module[{q=DerivativeDivides[ActivateTrig[y],ActivateTrig[u],x]},
    q*Log[RemoveContent[ActivateTrig[y],x]] /;
 Not[FalseQ[q]]] /;
Not[InertTrigFreeQ[u]]


Int[u_/(y_*w_),x_Symbol] :=
  Module[{q=DerivativeDivides[ActivateTrig[y*w],ActivateTrig[u],x]},
    q*Log[RemoveContent[ActivateTrig[y*w],x]] /;
 Not[FalseQ[q]]] /;
Not[InertTrigFreeQ[u]]


Int[u_*y_^m_.,x_Symbol] :=
  Module[{q=DerivativeDivides[ActivateTrig[y],ActivateTrig[u],x]},
   q*ActivateTrig[y^(m+1)]/(m+1) /;
 Not[FalseQ[q]]] /;
FreeQ[m,x] && NonzeroQ[m+1] && Not[InertTrigFreeQ[u]]


Int[u_*y_^m_.*z_^n_.,x_Symbol] :=
  Module[{q=DerivativeDivides[ActivateTrig[y*z],ActivateTrig[u*z^(n-m)],x]},
   q*ActivateTrig[y^(m+1)*z^(m+1)]/(m+1) /;
 Not[FalseQ[q]]] /;
FreeQ[{m,n},x] && NonzeroQ[m+1] && Not[InertTrigFreeQ[u]]


If[ShowSteps,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Tan[a+b*x]],x]","1/b*Subst[Int[F[x]/(1+x^2),x],x,Tan[a+b*x]]",Hold[
  Module[{d=FreeFactors[Tan[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d],x]]]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x]] /;
SimplifyFlag && InverseFunctionFreeQ[u,x],

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  Module[{d=FreeFactors[Tan[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d],x]] /;
 NotFalseQ[v] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x]] /;
InverseFunctionFreeQ[u,x]]


Int[u_.*(a_.*tan[c_.+d_.*x_]^n_.+b_.*sec[c_.+d_.*x_]^n_.)^p_,x_Symbol] :=
  Int[ActivateTrig[u]*Sec[c+d*x]^(n*p)*(b+a*Sin[c+d*x]^n)^p,x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p]


Int[u_.*(a_.*cot[c_.+d_.*x_]^n_.+b_.*csc[c_.+d_.*x_]^n_.)^p_,x_Symbol] :=
  Int[ActivateTrig[u]*Csc[c+d*x]^(n*p)*(b+a*Cos[c+d*x]^n)^p,x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p]


Int[u_*(a_*F_[c_.+d_.*x_]^p_.+b_.*F_[c_.+d_.*x_]^q_.)^n_.,x_Symbol] :=
  Int[ActivateTrig[u*F[c+d*x]^(n*p)*(a+b*F[c+d*x]^(q-p))^n],x] /;
FreeQ[{a,b,c,d,p,q},x] && InertTrigQ[F] && IntegerQ[n] && PosQ[q-p]


Int[u_*(a_*F_[d_.+e_.*x_]^p_.+b_.*F_[d_.+e_.*x_]^q_.+c_.*F_[d_.+e_.*x_]^r_.)^n_.,x_Symbol] :=
  Int[ActivateTrig[u*F[d+e*x]^(n*p)*(a+b*F[d+e*x]^(q-p)+c*F[d+e*x]^(r-p))^n],x] /;
FreeQ[{a,b,c,d,e,p,q,r},x] && InertTrigQ[F] && IntegerQ[n] && PosQ[q-p] && PosQ[r-p]


Int[u_*(a_+b_.*F_[d_.+e_.*x_]^p_.+c_.*F_[d_.+e_.*x_]^q_.)^n_.,x_Symbol] :=
  Int[ActivateTrig[u*F[d+e*x]^(n*p)*(b+a*F[d+e*x]^(-p)+c*F[d+e*x]^(q-p))^n],x] /;
FreeQ[{a,b,c,d,e,p,q},x] && InertTrigQ[F] && IntegerQ[n] && NegQ[p]


Int[u_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(a*E^(-a/b*(c+d*x)))^n,x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2]


Int[u_,x_Symbol] :=
  Int[TrigSimplify[u],x] /;
TrigSimplifyQ[u]


Int[(u_*v_)^n_,x_Symbol] :=
  Module[{uu=ActivateTrig[u],vv=ActivateTrig[v]},
  Sqrt[uu*vv]/(Sqrt[uu]*Sqrt[vv])*Int[uu^n*vv^n,x]] /;
(Not[InertTrigFreeQ[u]] || Not[InertTrigFreeQ[v]]) && IntegerQ[n-1/2]


Int[(u_*v_)^n_,x_Symbol] :=
  Module[{uu=ActivateTrig[u],vv=ActivateTrig[v]},
  (uu*vv)^n/(uu^n*vv^n)*Int[uu^n*vv^n,x]] /;
(Not[InertTrigFreeQ[u]] || Not[InertTrigFreeQ[v]]) && Not[IntegerQ[n-1/2]]


Int[u_,x_Symbol] :=
  Module[{v=ExpandTrig[u,x]},
  Int[v,x] /;
 SumQ[v]] /;
Not[InertTrigFreeQ[u]]


If[ShowSteps,

Int[u_,x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, 
			Int[SubstFor[1/(1+FreeFactors[Tan[FunctionOfTrig[u,x]/2],x]^2*x^2),Tan[FunctionOfTrig[u,x]/2]/FreeFactors[Tan[FunctionOfTrig[u,x]/2],x],u,x],x]]},  
  ShowStep["","Int[F[Sin[a+b*x],Cos[a+b*x]],x]","2/b*Subst[Int[1/(1+x^2)*F[2*x/(1+x^2),(1-x^2)/(1+x^2)],x],x,Tan[(a+b*x)/2]]",Hold[
  Module[{v=FunctionOfTrig[u,x],d},
  d=FreeFactors[Tan[v/2],x];
  Dist[2*d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d],x]]]] /;
 FreeQ[w,Int]] /;
SimplifyFlag && InverseFunctionFreeQ[u,x] && NotFalseQ[FunctionOfTrig[u,x]],

Int[u_,x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, 
			Int[SubstFor[1/(1+FreeFactors[Tan[FunctionOfTrig[u,x]/2],x]^2*x^2),Tan[FunctionOfTrig[u,x]/2]/FreeFactors[Tan[FunctionOfTrig[u,x]/2],x],u,x],x]]},  
  Module[{v=FunctionOfTrig[u,x],d},
  d=FreeFactors[Tan[v/2],x];
  Dist[2*d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d],x]] /;
 FreeQ[w,Int]] /;
InverseFunctionFreeQ[u,x] && NotFalseQ[FunctionOfTrig[u,x]]]


(* If[ShowSteps,

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Sin[a+b*x],Cos[a+b*x]],x]","2/b*Subst[Int[1/(1+x^2)*F[2*x/(1+x^2),(1-x^2)/(1+x^2)],x],x,Tan[(a+b*x)/2]]",Hold[
  Module[{d=FreeFactors[Tan[v/2],x]},
  Dist[2*d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d],x]]]] /;
 NotFalseQ[v]] /;
SimplifyFlag && InverseFunctionFreeQ[u,x],

Int[u_,x_Symbol] :=
  Module[{v=FunctionOfTrig[u,x]},
  Module[{d=FreeFactors[Tan[v/2],x]},
  Dist[2*d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d],x]] /;
 NotFalseQ[v]] /;
InverseFunctionFreeQ[u,x]] *)


Int[u_,x_Symbol] :=
  Module[{v=ActivateTrig[u]},
   Defer[Int][v,x]] /;
Not[InertTrigFreeQ[u]]


(* ::Subsection::Closed:: *)
(*9.1 (c+d x)^m trig(a+b x)^n*)


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_],x_Symbol] :=
  -(c+d*x)^m*Cos[a+b*x]/b + 
  d*m/b*Int[(c+d*x)^(m-1)*Cos[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Cos[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*Sin[a+b*x]/b - 
  d*m/b*Int[(c+d*x)^(m-1)*Sin[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[Sin[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  SinIntegral[b*c/d+b*x]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d]


Int[Cos[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  CosIntegral[b*c/d+b*x]/d /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d]


Int[Sin[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Cos[(b*c-a*d)/d]*Int[Sin[b*c/d+b*x]/(c+d*x),x] - 
  Sin[(b*c-a*d)/d]*Int[Cos[b*c/d+b*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[Cos[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Cos[(b*c-a*d)/d]*Int[Cos[b*c/d+b*x]/(c+d*x),x] + 
  Sin[(b*c-a*d)/d]*Int[Sin[b*c/d+b*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[Sin[a_.+b_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  2/d*Subst[Int[Sin[b*x^2/d],x],x,Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d]


Int[Cos[a_.+b_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  2/d*Subst[Int[Cos[b*x^2/d],x],x,Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c-a*d]


Int[Sin[a_.+b_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  Cos[(b*c-a*d)/d]*Int[Sin[b*c/d+b*x]/Sqrt[c+d*x],x] - 
  Sin[(b*c-a*d)/d]*Int[Cos[b*c/d+b*x]/Sqrt[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[Cos[a_.+b_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  Cos[(b*c-a*d)/d]*Int[Cos[b*c/d+b*x]/Sqrt[c+d*x],x] + 
  Sin[(b*c-a*d)/d]*Int[Sin[b*c/d+b*x]/Sqrt[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[(c_.+d_.*x_)^m_*Sin[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Sin[a+b*x]/(d*(m+1)) -
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Cos[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1


Int[(c_.+d_.*x_)^m_*Cos[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Cos[a+b*x]/(d*(m+1)) +
  b/(d*(m+1))*Int[(c+d*x)^(m+1)*Sin[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_],x_Symbol] :=
  I/2*Int[(c+d*x)^m*E^(-a*I-b*I*x),x] - 
  I/2*Int[(c+d*x)^m*E^(a*I+b*I*x),x] /;
FreeQ[{a,b,c,d,m},x]


Int[(c_.+d_.*x_)^m_.*Cos[a_.+b_.*x_],x_Symbol] :=
  1/2*Int[(c+d*x)^m*E^(-a*I-b*I*x),x] + 
  1/2*Int[(c+d*x)^m*E^(a*I+b*I*x),x] /;
FreeQ[{a,b,c,d,m},x]


Int[(c_.+d_.*x_)*Sin[a_.+b_.*x_]^n_,x_Symbol] :=
  d*Sin[a+b*x]^n/(b^2*n^2) -
  (c+d*x)*Cos[a+b*x]*Sin[a+b*x]^(n-1)/(b*n) +
  (n-1)/n*Int[(c+d*x)*Sin[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1


Int[(c_.+d_.*x_)*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
  d*Cos[a+b*x]^n/(b^2*n^2) +
  (c+d*x)*Sin[a+b*x]*Cos[a+b*x]^(n-1)/(b*n) +
  (n-1)/n*Int[(c+d*x)*Cos[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1


Int[(c_.+d_.*x_)^m_*Sin[a_.+b_.*x_]^2,x_Symbol] :=
  d*m*(c+d*x)^(m-1)*Sin[a+b*x]^2/(4*b^2) - 
  (c+d*x)^m*Cos[a+b*x]*Sin[a+b*x]/(2*b) + 
  (c+d*x)^(m+1)/(2*d*(m+1)) - 
  d^2*m*(m-1)/(4*b^2)*Int[(c+d*x)^(m-2)*Sin[a+b*x]^2,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>1


Int[(c_.+d_.*x_)^m_*Cos[a_.+b_.*x_]^2,x_Symbol] :=
  d*m*(c+d*x)^(m-1)*Cos[a+b*x]^2/(4*b^2) + 
  (c+d*x)^m*Sin[a+b*x]*Cos[a+b*x]/(2*b) + 
  (c+d*x)^(m+1)/(2*d*(m+1)) - 
  d^2*m*(m-1)/(4*b^2)*Int[(c+d*x)^(m-2)*Cos[a+b*x]^2,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>1


Int[(c_.+d_.*x_)^m_*Sin[a_.+b_.*x_]^n_,x_Symbol] :=
  d*m*(c+d*x)^(m-1)*Sin[a+b*x]^n/(b^2*n^2) -
  (c+d*x)^m*Cos[a+b*x]*Sin[a+b*x]^(n-1)/(b*n) +
  (n-1)/n*Int[(c+d*x)^m*Sin[a+b*x]^(n-2),x] -
  d^2*m*(m-1)/(b^2*n^2)*Int[(c+d*x)^(m-2)*Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m>1 && n!=2


Int[(c_.+d_.*x_)^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
  d*m*(c+d*x)^(m-1)*Cos[a+b*x]^n/(b^2*n^2) +
  (c+d*x)^m*Sin[a+b*x]*Cos[a+b*x]^(n-1)/(b*n) +
  (n-1)/n*Int[(c+d*x)^m*Cos[a+b*x]^(n-2),x] -
  d^2*m*(m-1)/(b^2*n^2)*Int[(c+d*x)^(m-2)*Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m>1 && n!=2


Int[(c_.+d_.*x_)^m_*Sin[a_.+b_.*x_]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Sin[a+b*x]^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && n>1 && (Not[RationalQ[m]] || -1<=m<1)


Int[(c_.+d_.*x_)^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Cos[a+b*x]^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && n>1 && (Not[RationalQ[m]] || -1<=m<1)


Int[(c_.+d_.*x_)^m_*Sin[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Sin[a+b*x]^n/(d*(m+1)) - 
  b*n/(d*(m+1))*Int[ExpandTrigReduce[(c+d*x)^(m+1),Cos[a+b*x]*Sin[a+b*x]^(n-1),x],x] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && n>1 && RationalQ[m] && -2<=m<-1


Int[(c_.+d_.*x_)^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Cos[a+b*x]^n/(d*(m+1)) + 
  b*n/(d*(m+1))*Int[ExpandTrigReduce[(c+d*x)^(m+1),Sin[a+b*x]*Cos[a+b*x]^(n-1),x],x] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && n>1 && RationalQ[m] && -2<=m<-1


Int[(c_.+d_.*x_)^m_*Sin[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Sin[a+b*x]^n/(d*(m+1)) - 
  b*n*(c+d*x)^(m+2)*Cos[a+b*x]*Sin[a+b*x]^(n-1)/(d^2*(m+1)*(m+2)) - 
  b^2*n^2/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*Sin[a+b*x]^n,x] + 
  b^2*n*(n-1)/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*Sin[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m<-2


Int[(c_.+d_.*x_)^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Cos[a+b*x]^n/(d*(m+1)) + 
  b*n*(c+d*x)^(m+2)*Sin[a+b*x]*Cos[a+b*x]^(n-1)/(d^2*(m+1)*(m+2)) - 
  b^2*n^2/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*Cos[a+b*x]^n,x] + 
  b^2*n*(n-1)/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*Cos[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m<-2


Int[(c_.+d_.*x_)*Sin[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)*Cos[a+b*x]*Sin[a+b*x]^(n+1)/(b*(n+1)) -
  d*Sin[a+b*x]^(n+2)/(b^2*(n+1)*(n+2)) +
  (n+2)/(n+1)*Int[(c+d*x)*Sin[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1 && n!=-2


Int[(c_.+d_.*x_)*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)*Sin[a+b*x]*Cos[a+b*x]^(n+1)/(b*(n+1)) -
  d*Cos[a+b*x]^(n+2)/(b^2*(n+1)*(n+2)) +
  (n+2)/(n+1)*Int[(c+d*x)*Cos[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1 && n!=-2


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^m*Cos[a+b*x]*Sin[a+b*x]^(n+1)/(b*(n+1)) -
  d*m*(c+d*x)^(m-1)*Sin[a+b*x]^(n+2)/(b^2*(n+1)*(n+2)) +
  (n+2)/(n+1)*Int[(c+d*x)^m*Sin[a+b*x]^(n+2),x] +
  d^2*m*(m-1)/(b^2*(n+1)*(n+2))*Int[(c+d*x)^(m-2)*Sin[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n<-1 && n!=-2 && m>1


Int[(c_.+d_.*x_)^m_.*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)^m*Sin[a+b*x]*Cos[a+b*x]^(n+1)/(b*(n+1)) -
  d*m*(c+d*x)^(m-1)*Cos[a+b*x]^(n+2)/(b^2*(n+1)*(n+2)) +
  (n+2)/(n+1)*Int[(c+d*x)^m*Cos[a+b*x]^(n+2),x] +
  d^2*m*(m-1)/(b^2*(n+1)*(n+2))*Int[(c+d*x)^(m-2)*Cos[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n<-1 && n!=-2 && m>1


Int[(c_.+d_.*x_)^m_.*Tan[a_.+b_.*x_],x_Symbol] :=
  -I*(c+d*x)^(m+1)/(d*(m+1)) + 
  2*I*Int[(c+d*x)^m/(1+E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*Cot[a_.+b_.*x_],x_Symbol] :=
  I*(c+d*x)^(m+1)/(d*(m+1)) - 
  2*I*Int[(c+d*x)^m/(1-E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^m*Tan[a+b*x]^(n-1)/(b*(n-1)) - 
  d*m/(b*(n-1))*Int[(c+d*x)^(m-1)*Tan[a+b*x]^(n-1),x] - 
  Int[(c+d*x)^m*Tan[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m>0


Int[(c_.+d_.*x_)^m_.*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)^m*Cot[a+b*x]^(n-1)/(b*(n-1)) + 
  d*m/(b*(n-1))*Int[(c+d*x)^(m-1)*Cot[a+b*x]^(n-1),x] - 
  Int[(c+d*x)^m*Cot[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && m>0


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_],x_Symbol] :=
  -2*I*(c+d*x)^m*ArcTan[E^(I*a+I*b*x)]/b - 
  d*m/b*Int[(c+d*x)^(m-1)*Log[1-I*E^(I*(a+b*x))],x] + 
  d*m/b*Int[(c+d*x)^(m-1)*Log[1+I*E^(I*(a+b*x))],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_],x_Symbol] :=
  -2*(c+d*x)^m*ArcTanh[E^(I*a+I*b*x)]/b - 
  d*m/b*Int[(c+d*x)^(m-1)*Log[1-E^(I*(a+b*x))],x] + 
  d*m/b*Int[(c+d*x)^(m-1)*Log[1+E^(I*(a+b*x))],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^2,x_Symbol] :=
  (c+d*x)^m*Tan[a+b*x]/b - 
  d*m/b*Int[(c+d*x)^(m-1)*Tan[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^2,x_Symbol] :=
  -(c+d*x)^m*Cot[a+b*x]/b + 
  d*m/b*Int[(c+d*x)^(m-1)*Cot[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)*Tan[a+b*x]*Sec[a+b*x]^(n-2)/(b*(n-1)) -
  d*Sec[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  (n-2)/(n-1)*Int[(c+d*x)*Sec[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1 && n!=2


Int[(c_.+d_.*x_)*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)*Cot[a+b*x]*Csc[a+b*x]^(n-2)/(b*(n-1)) -
  d*Csc[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  (n-2)/(n-1)*Int[(c+d*x)*Csc[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n>1 && n!=2


Int[(c_.+d_.*x_)^m_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
  (c+d*x)^m*Tan[a+b*x]*Sec[a+b*x]^(n-2)/(b*(n-1)) -
  d*m*(c+d*x)^(m-1)*Sec[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  (n-2)/(n-1)*Int[(c+d*x)^m*Sec[a+b*x]^(n-2),x] +
  d^2*m*(m-1)/(b^2*(n-1)*(n-2))*Int[(c+d*x)^(m-2)*Sec[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && n!=2 && m>1


Int[(c_.+d_.*x_)^m_*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
  -(c+d*x)^m*Cot[a+b*x]*Csc[a+b*x]^(n-2)/(b*(n-1)) -
  d*m*(c+d*x)^(m-1)*Csc[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  (n-2)/(n-1)*Int[(c+d*x)^m*Csc[a+b*x]^(n-2),x] +
  d^2*m*(m-1)/(b^2*(n-1)*(n-2))*Int[(c+d*x)^(m-2)*Csc[a+b*x]^(n-2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n>1 && n!=2 && m>1


Int[(c_.+d_.*x_)*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
  d*Sec[a+b*x]^n/(b^2*n^2) -
  (c+d*x)*Sin[a+b*x]*Sec[a+b*x]^(n+1)/(b*n) +
  (n+1)/n*Int[(c+d*x)*Sec[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1


Int[(c_.+d_.*x_)*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
  d*Csc[a+b*x]^n/(b^2*n^2) +
  (c+d*x)*Cos[a+b*x]*Csc[a+b*x]^(n+1)/(b*n) +
  (n+1)/n*Int[(c+d*x)*Csc[a+b*x]^(n+2),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n] && n<-1


Int[(c_.+d_.*x_)^m_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
  d*m*(c+d*x)^(m-1)*Sec[a+b*x]^n/(b^2*n^2) -
  (c+d*x)^m*Sin[a+b*x]*Sec[a+b*x]^(n+1)/(b*n) +
  (n+1)/n*Int[(c+d*x)^m*Sec[a+b*x]^(n+2),x] -
  d^2*m*(m-1)/(b^2*n^2)*Int[(c+d*x)^(m-2)*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n<-1 && m>1


Int[(c_.+d_.*x_)^m_*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
  d*m*(c+d*x)^(m-1)*Csc[a+b*x]^n/(b^2*n^2) +
  (c+d*x)^m*Cos[a+b*x]*Csc[a+b*x]^(n+1)/(b*n) +
  (n+1)/n*Int[(c+d*x)^m*Csc[a+b*x]^(n+2),x] -
  d^2*m*(m-1)/(b^2*n^2)*Int[(c+d*x)^(m-2)*Csc[a+b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m,n] && n<-1 && m>1


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
  Cos[a+b*x]^n*Sec[a+b*x]^n*Int[(c+d*x)^m/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
  Sin[a+b*x]^n*Csc[a+b*x]^n*Int[(c+d*x)^m/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[n]]


Int[u_^m_.*F_[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F[ExpandToSum[v,x]]^n,x] /;
FreeQ[{m,n},x] && TrigQ[F] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Cos[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*Sin[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Sin[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]*Cos[a_.+b_.*x_]^n_.,x_Symbol] :=
  -(c+d*x)^m*Cos[a+b*x]^(n+1)/(b*(n+1)) + 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Cos[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Cos[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Sin[a+b*x]^n*Cos[a+b*x]^p,x],x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
  -Int[(c+d*x)^m*Sin[a+b*x]^n*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sin[a+b*x]^(n-2)*Tan[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Cos[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
  -Int[(c+d*x)^m*Cos[a+b*x]^n*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Cos[a+b*x]^(n-2)*Cot[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
  (c+d*x)^m*Sec[a+b*x]^n/(b*n) - 
  d*m/(b*n)*Int[(c+d*x)^(m-1)*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && p===1 && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
  -(c+d*x)^m*Csc[a+b*x]^n/(b*n) + 
  d*m/(b*n)*Int[(c+d*x)^(m-1)*Csc[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && p===1 && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^2*Tan[a_.+b_.*x_]^n_.,x_Symbol] :=
  (c+d*x)^m*Tan[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n +1))*Int[(c+d*x)^(m-1)*Tan[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^2*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  -(c+d*x)^m*Cot[a+b*x]^(n+1)/(b*(n+1)) + 
  d*m/(b*(n +1))*Int[(c+d*x)^(m-1)*Cot[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]*Tan[a_.+b_.*x_]^p_,x_Symbol] :=
  -Int[(c+d*x)^m*Sec[a+b*x]*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sec[a+b*x]^3*Tan[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_,x_Symbol] :=
  -Int[(c+d*x)^m*Sec[a+b*x]^n*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sec[a+b*x]^(n+2)*Tan[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]*Cot[a_.+b_.*x_]^p_,x_Symbol] :=
  -Int[(c+d*x)^m*Csc[a+b*x]*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csc[a+b*x]^3*Cot[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_,x_Symbol] :=
  -Int[(c+d*x)^m*Csc[a+b*x]^n*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csc[a+b*x]^(n+2)*Cot[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[Sec[a+b*x]^n*Tan[a+b*x]^p,x]]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d,n,p},x] && PositiveIntegerQ[m] && (EvenQ[n] || OddQ[p])


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[Csc[a+b*x]^n*Cot[a+b*x]^p,x]]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d,n,p},x] && PositiveIntegerQ[m] && (EvenQ[n] || OddQ[p])


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Sec[a_.+b_.*x_]^n_., x_Symbol] :=
  2^n*Int[(c+d*x)^m*Csc[2*a+2*b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && IntegerQ[n]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Sec[a_.+b_.*x_]^p_., x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[Csc[a+b*x]^n*Sec[a+b*x]^p,x]]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && RationalQ[m] && m>0 && n!=p


Int[u_^m_.*F_[v_]^n_.*G_[w_]^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F[ExpandToSum[v,x]]^n*G[ExpandToSum[v,x]]^p,x] /;
FreeQ[{m,n,p},x] && TrigQ[F] && TrigQ[G] && ZeroQ[v-w] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]*(a_+b_.*Sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]*(a_+b_.*Cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]^2*(a_+b_.*Tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]^2*(a_+b_.*Cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]*Tan[c_.+d_.*x_]*(a_+b_.*Sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]*Cot[c_.+d_.*x_]*(a_+b_.*Csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NonzeroQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]^p_.*Sin[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Sin[a+b*x]^p*Sin[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[p,q] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]^p_.*Cos[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Cos[a+b*x]^p*Cos[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[p,q] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]^p_.*Cos[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Sin[a+b*x]^p*Cos[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[p,q]


Int[(e_.+f_.*x_)^m_.*F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigExpand[(e+f*x)^m*G[c+d*x]^q,F,c+d*x,p,b/d,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && MemberQ[{Sin,Cos},F] && MemberQ[{Sec,Csc},G] && 
  PositiveIntegerQ[p,q] && ZeroQ[b*c-a*d] && PositiveIntegerQ[b/d-1]


(* ::Subsection::Closed:: *)
(*9.2 x^m trig(a+b x^n)^p*)


Int[Sin[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Module[{g=Numerator[1/n]},
  g*Subst[Int[x^(g-1)*Sin[a+b*x^(n*g)]^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,p},x] && RationalQ[n] && (n<0 || FractionQ[n])


Int[Cos[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Module[{g=Numerator[1/n]},
  g*Subst[Int[x^(g-1)*Cos[a+b*x^(n*g)]^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,p},x] && RationalQ[n] && (n<0 || FractionQ[n])


Int[Sin[b_.*x_^2],x_Symbol] :=
  Sqrt[Pi/2]/Rt[b,2]*FresnelS[Sqrt[2/Pi]*Rt[b,2]*x] /;
FreeQ[b,x]


Int[Cos[b_.*x_^2],x_Symbol] :=
  Sqrt[Pi/2]/Rt[b,2]*FresnelC[Sqrt[2/Pi]*Rt[b,2]*x] /;
FreeQ[b,x]


Int[Sin[c_.*(a_.+b_.*x_)^2],x_Symbol] :=
  Sqrt[Pi/2]/(b*Rt[c,2])*FresnelS[Sqrt[2/Pi]*Rt[c,2]*(a+b*x)] /;
FreeQ[{a,b,c},x]


Int[Cos[c_.*(a_.+b_.*x_)^2],x_Symbol] :=
  Sqrt[Pi/2]/(b*Rt[c,2])*FresnelC[Sqrt[2/Pi]*Rt[c,2]*(a+b*x)] /;
FreeQ[{a,b,c},x]


Int[Sin[a_+b_.*x_^2],x_Symbol] :=
  Sin[a]*Int[Cos[b*x^2],x] + 
  Cos[a]*Int[Sin[b*x^2],x] /;
FreeQ[{a,b},x]


Int[Cos[a_+b_.*x_^2],x_Symbol] :=
  Cos[a]*Int[Cos[b*x^2],x] - 
  Sin[a]*Int[Sin[b*x^2],x] /;
FreeQ[{a,b},x]


Int[Sin[a_.+b_.*x_^n_],x_Symbol] :=
  I/2*Int[E^(-a*I-b*I*x^n),x] - 
  I/2*Int[E^(a*I+b*I*x^n),x] /;
FreeQ[{a,b,n},x] && NonzeroQ[n-2]


Int[Cos[a_.+b_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(-a*I-b*I*x^n),x] + 
  1/2*Int[E^(a*I+b*I*x^n),x] /;
FreeQ[{a,b,n},x] && NonzeroQ[n-2]


Int[Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  Int[ExpandTrigReduce[Sin[a+b*x^n]^p,x],x] /;
FreeQ[{a,b,n},x] && IntegerQ[p] && p>1


Int[Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  Int[ExpandTrigReduce[Cos[a+b*x^n]^p,x],x] /;
FreeQ[{a,b,n},x] && IntegerQ[p] && p>1


Int[Sin[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Defer[Int][Sin[a+b*x^n]^p,x] /;
FreeQ[{a,b,n,p},x]


Int[Cos[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Defer[Int][Cos[a+b*x^n]^p,x] /;
FreeQ[{a,b,n,p},x]


Int[Sin[a_.+b_.*u_^n_]^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[Sin[a+b*x^n]^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[Cos[a_.+b_.*u_^n_]^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[Cos[a+b*x^n]^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[Sin[b_.*x_^n_]/x_,x_Symbol] :=
  SinIntegral[b*x^n]/n /;
FreeQ[{b,n},x]


Int[Cos[b_.*x_^n_]/x_,x_Symbol] :=
  CosIntegral[b*x^n]/n /;
FreeQ[{b,n},x]


Int[Sin[a_+b_.*x_^n_]/x_,x_Symbol] :=
  Sin[a]*Int[Cos[b*x^n]/x,x] + 
  Cos[a]*Int[Sin[b*x^n]/x,x] /;
FreeQ[{a,b,n},x]


Int[Cos[a_+b_.*x_^n_]/x_,x_Symbol] :=
  Cos[a]*Int[Cos[b*x^n]/x,x] - 
  Sin[a]*Int[Sin[b*x^n]/x,x] /;
FreeQ[{a,b,n},x]


Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
  -Cos[a+b*x^n]/(b*n) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-(n-1)]


Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
  Sin[a+b*x^n]/(b*n) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-(n-1)]


Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
  2/n*Subst[Int[Sin[a+b*x^2],x],x,x^(n/2)] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-(n/2-1)]


Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
  2/n*Subst[Int[Cos[a+b*x^2],x],x,x^(n/2)] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-(n/2-1)]


Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
  -x^(m-n+1)*Cos[a+b*x^n]/(b*n) + 
  (m-n+1)/(b*n)*Int[x^(m-n)*Cos[a+b*x^n],x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && (0<n<m+1 || m+1<n<0)


Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
  Module[{mn=Simplify[m-n]},
  -x^(mn+1)*Cos[a+b*x^n]/(b*n) + 
  (mn+1)/(b*n)*Int[x^mn*Cos[a+b*x^n],x]] /;
FreeQ[{a,b,m,n},x] && NonzeroQ[m-n+1] && PositiveIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m-n+1)*Sin[a+b*x^n]/(b*n) - 
  (m-n+1)/(b*n)*Int[x^(m-n)*Sin[a+b*x^n],x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && (0<n<m+1 || m+1<n<0)


Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
  Module[{mn=Simplify[m-n]},
  x^(mn+1)*Sin[a+b*x^n]/(b*n) - 
  (mn+1)/(b*n)*Int[x^mn*Sin[a+b*x^n],x]] /;
FreeQ[{a,b,m,n},x] && NonzeroQ[m-n+1] && PositiveIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*Sin[a+b*x^n]/(m+1) -
  b*n/(m+1)*Int[x^(m+n)*Cos[a+b*x^n],x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && (n>0 && m<-1 || n<0 && m>-1)


Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*Sin[a+b*x^n]/(m+1) -
  b*n/(m+1)*Int[x^Simplify[m+n]*Cos[a+b*x^n],x] /;
FreeQ[{a,b,m,n},x] && NegativeIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*Cos[a+b*x^n]/(m+1) +
  b*n/(m+1)*Int[x^(m+n)*Sin[a+b*x^n],x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && (n>0 && m<-1 || n<0 && m>-1)


Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*Cos[a+b*x^n]/(m+1) +
  b*n/(m+1)*Int[x^Simplify[m+n]*Sin[a+b*x^n],x] /;
FreeQ[{a,b,m,n},x] && NegativeIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
  I/2*Int[x^m*E^(-a*I-b*I*x^n),x] - 
  I/2*Int[x^m*E^(a*I+b*I*x^n),x] /;
FreeQ[{a,b,m,n},x]


Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
  1/2*Int[x^m*E^(-a*I-b*I*x^n),x] + 
  1/2*Int[x^m*E^(a*I+b*I*x^n),x] /;
FreeQ[{a,b,m,n},x]


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -Sin[a+b*x^n]^p/((n-1)*x^(n-1)) +
  b*n*p/(n-1)*Int[Sin[a+b*x^n]^(p-1)*Cos[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && ZeroQ[m+n] && p>1 && NonzeroQ[n-1]


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -Cos[a+b*x^n]^p/((n-1)*x^(n-1)) -
  b*n*p/(n-1)*Int[Cos[a+b*x^n]^(p-1)*Sin[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && ZeroQ[m+n] && p>1 && NonzeroQ[n-1]


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  n*Sin[a+b*x^n]^p/(b^2*n^2*p^2) -
  x^n*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Sin[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-2*n+1] && RationalQ[p] && p>1


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  n*Cos[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^n*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Cos[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-2*n+1] && RationalQ[p] && p>1


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  (m-n+1)*x^(m-2*n+1)*Sin[a+b*x^n]^p/(b^2*n^2*p^2) -
  x^(m-n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Sin[a+b*x^n]^(p-2),x] -
  (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2)*Int[x^(m-2*n)*Sin[a+b*x^n]^p,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<m+1


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  (m-n+1)*x^(m-2*n+1)*Cos[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^(m-n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Cos[a+b*x^n]^(p-2),x] -
  (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2)*Int[x^(m-2*n)*Cos[a+b*x^n]^p,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<m+1


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m+1)*Sin[a+b*x^n]^p/(m+1) - 
  b*n*p*x^(m+n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) - 
  b^2*n^2*p^2/((m+1)*(m+n+1))*Int[x^(m+2*n)*Sin[a+b*x^n]^p,x] + 
  b^2*n^2*p*(p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*Sin[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<1-m && NonzeroQ[m+n+1]


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m+1)*Cos[a+b*x^n]^p/(m+1) + 
  b*n*p*x^(m+n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) - 
  b^2*n^2*p^2/((m+1)*(m+n+1))*Int[x^(m+2*n)*Cos[a+b*x^n]^p,x] + 
  b^2*n^2*p*(p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*Cos[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<1-m && NonzeroQ[m+n+1]


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[Sin[a+b*x^Simplify[n/(m+1)]]^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]]


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[Cos[a+b*x^Simplify[n/(m+1)]]^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]]


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sin[a+b*x^n]^p,x],x] /;
FreeQ[{a,b,m,n},x] && IntegerQ[p] && p>1 && Not[FractionQ[m]] && Not[FractionQ[n]]


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Cos[a+b*x^n]^p,x],x] /;
FreeQ[{a,b,m,n},x] && IntegerQ[p] && p>1 && Not[FractionQ[m]] && Not[FractionQ[n]]


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^n*Cos[a+b*x^n]*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  n*Sin[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) + 
  (p+2)/(p+1)*Int[x^m*Sin[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-2*n+1] && RationalQ[p] && p<-1 && p!=-2


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^n*Sin[a+b*x^n]*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  n*Cos[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) + 
  (p+2)/(p+1)*Int[x^m*Cos[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-2*n+1] && RationalQ[p] && p<-1 && p!=-2


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m-n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)*x^(m-2*n+1)*Sin[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (p+2)/(p+1)*Int[x^m*Sin[a+b*x^n]^(p+2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2))*Int[x^(m-2*n)*Sin[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p<-1 && p!=-2 && 0<2*n<m+1 


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^(m-n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)*x^(m-2*n+1)*Cos[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (p+2)/(p+1)*Int[x^m*Cos[a+b*x^n]^(p+2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2))*Int[x^(m-2*n)*Cos[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p<-1 && p!=-2 && 0<2*n<m+1 


Int[x_^m_.*Sin[a_.+b_.*u_^n_]^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*Sin[a+b*x^n]^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && IntegerQ[m] && NonzeroQ[u-x]


Int[x_^m_.*Cos[a_.+b_.*u_^n_]^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*Cos[a+b*x^n]^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && IntegerQ[m] && NonzeroQ[u-x]


Int[x_^m_.*Sin[a_.+b_.*x_^n_.]^p_.*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
  Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-n+1] && NonzeroQ[p+1]


Int[x_^m_.*Cos[a_.+b_.*x_^n_.]^p_.*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
  -Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-n+1] && NonzeroQ[p+1]


Int[x_^m_.*Sin[a_.+b_.*x_^n_.]^p_.*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
  x^(m-n+1)*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Sin[a+b*x^n]^(p+1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m,n] && 0<n<m+1 && NonzeroQ[p+1]


Int[x_^m_.*Cos[a_.+b_.*x_^n_.]^p_.*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) +
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Cos[a+b*x^n]^(p+1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m,n] && 0<n<m+1 && NonzeroQ[p+1]


Int[x_^m_.*Tan[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[Tan[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-(n-1)]


Int[x_^m_.*Cot[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[Cot[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-(n-1)]


Int[x_^m_.*Tan[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m-n+1)*Tan[a+b*x^n]^(p-1)/(b*n*(p-1)) - 
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Tan[a+b*x^n]^(p-1),x] - 
  Int[x^m*Tan[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p>1 && 0<n<m+1


Int[x_^m_.*Cot[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^(m-n+1)*Cot[a+b*x^n]^(p-1)/(b*n*(p-1)) + 
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Cot[a+b*x^n]^(p-1),x] - 
  Int[x^m*Cot[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p>1 && 0<n<m+1


Int[x_^m_.*Tan[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m-n+1)*Tan[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Tan[a+b*x^n]^(p+1),x] - 
  Int[x^m*Tan[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p<-1 && 0<n<m+1


Int[x_^m_.*Cot[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^(m-n+1)*Cot[a+b*x^n]^(p+1)/(b*n*(p+1)) + 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Cot[a+b*x^n]^(p+1),x] - 
  Int[x^m*Cot[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p] && p<-1 && 0<n<m+1


Int[Sec[a_.+b_.*x_^n_],x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*Sec[a+b*x],x],x,x^n] /;
FreeQ[{a,b},x] && PositiveIntegerQ[1/n]


Int[Csc[a_.+b_.*x_^n_],x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*Csc[a+b*x],x],x,x^n] /;
FreeQ[{a,b},x] && PositiveIntegerQ[1/n]


Int[x_^m_.*Sec[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*Sec[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Csc[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*Csc[a+b*x]^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Sec[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Defer[Int][x^m*Sec[a+b*x^n]^p,x] /;
FreeQ[{a,b,m,n,p},x]


Int[x_^m_.*Csc[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
  Defer[Int][x^m*Csc[a+b*x^n]^p,x] /;
FreeQ[{a,b,m,n,p},x]


Int[x_^m_.*Sec[a_.+b_.*x_^n_.]^p_*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
  x^(m-n+1)*Sec[a+b*x^n]^(p-1)/(b*n*(p-1)) -
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Sec[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]


Int[x_^m_.*Csc[a_.+b_.*x_^n_.]^p_*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Csc[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Csc[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]


Int[x_^m_.*Sec[a_.+b_.*x_^n_.]^p_.*Tan[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
  x^(m-n+1)*Sec[a+b*x^n]^p/(b*n*p) -
  (m-n+1)/(b*n*p)*Int[x^(m-n)*Sec[a+b*x^n]^p,x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1


Int[x_^m_.*Csc[a_.+b_.*x_^n_.]^p_.*Cot[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
  -x^(m-n+1)*Csc[a+b*x^n]^p/(b*n*p) +
  (m-n+1)/(b*n*p)*Int[x^(m-n)*Csc[a+b*x^n]^p,x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1


Int[F_[v_]^p_.,x_Symbol] :=
  Int[F[ExpandToSum[v,x]]^p,x] /;
FreeQ[p,x] && TrigQ[F] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[x_^m_.*F_[v_]^p_.,x_Symbol] :=
  Int[x^m*F[ExpandToSum[v,x]]^p,x] /;
FreeQ[{m,p},x] && TrigQ[F] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[(c_.*Sin[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Sin[a+b*x^n]^p]/Sin[a+b*x^n]^(p/2)*Int[Sin[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[(c_.*Cos[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Cos[a+b*x^n]^p]/Cos[a+b*x^n]^(p/2)*Int[Cos[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[(c_.*Sin[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Sin[a+b*x^n]^(p/2)/Sqrt[c*Sin[a+b*x^n]^p]*Int[Sin[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[(c_.*Cos[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Cos[a+b*x^n]^(p/2)/Sqrt[c*Cos[a+b*x^n]^p]*Int[Cos[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[(c_.*Sin[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  (c*Sin[a+b*x^n]^p)^q/Sin[a+b*x^n]^(p*q)*Int[Sin[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[(c_.*Cos[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  (c*Cos[a+b*x^n]^p)^q/Cos[a+b*x^n]^(p*q)*Int[Cos[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sin[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Sin[a+b*x^n]^p]/Sin[a+b*x^n]^(p/2)*Int[x^m*Sin[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Cos[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Cos[a+b*x^n]^p]/Cos[a+b*x^n]^(p/2)*Int[x^m*Cos[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sin[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Sin[a+b*x^n]^(p/2)/Sqrt[c*Sin[a+b*x^n]^p]*Int[x^m*Sin[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Cos[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Cos[a+b*x^n]^(p/2)/Sqrt[c*Cos[a+b*x^n]^p]*Int[x^m*Cos[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sin[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  (c*Sin[a+b*x^n]^p)^q/Sin[a+b*x^n]^(p*q)*Int[x^m*Sin[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Cos[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  (c*Cos[a+b*x^n]^p)^q/Cos[a+b*x^n]^(p*q)*Int[x^m*Cos[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[(c_.*Sec[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Sec[a+b*x^n]^p]/Sec[a+b*x^n]^(p/2)*Int[Sec[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[(c_.*Csc[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Csc[a+b*x^n]^p]/Csc[a+b*x^n]^(p/2)*Int[Csc[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[(c_.*Sec[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Sec[a+b*x^n]^(p/2)/Sqrt[c*Sec[a+b*x^n]^p]*Int[Sec[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[(c_.*Csc[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Csc[a+b*x^n]^(p/2)/Sqrt[c*Csc[a+b*x^n]^p]*Int[Csc[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && NegativeIntegerQ[q-1/2] && Not[OneQ[c,p]]


Int[(c_.*Sec[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  (c*Sec[a+b*x^n]^p)^q/Sec[a+b*x^n]^(p*q)*Int[Sec[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[(c_.*Csc[a_.+b_.*x_^n_]^p_.)^q_,x_Symbol] :=
  (c*Csc[a+b*x^n]^p)^q/Csc[a+b*x^n]^(p*q)*Int[Csc[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sec[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Sec[a+b*x^n]^p]/Sec[a+b*x^n]^(p/2)*Int[x^m*Sec[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Csc[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q-1/2)*Sqrt[c*Csc[a+b*x^n]^p]/Csc[a+b*x^n]^(p/2)*Int[x^m*Csc[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && PositiveIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sec[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Sec[a+b*x^n]^(p/2)/Sqrt[c*Sec[a+b*x^n]^p]*Int[x^m*Sec[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && NegativeIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Csc[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  c^(q+1/2)*Csc[a+b*x^n]^(p/2)/Sqrt[c*Csc[a+b*x^n]^p]*Int[x^m*Csc[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && NegativeIntegerQ[q+1/2] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Sec[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  (c*Sec[a+b*x^n]^p)^q/Sec[a+b*x^n]^(p*q)*Int[x^m*Sec[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[x_^m_.*(c_.*Csc[a_.+b_.*x_^n_.]^p_.)^q_,x_Symbol] :=
  (c*Csc[a+b*x^n]^p)^q/Csc[a+b*x^n]^(p*q)*Int[x^m*Csc[a+b*x^n]^(p*q),x] /;
FreeQ[{a,b,c,m,n,p,q},x] && Not[IntegerQ[q+1/2]] && Not[OneQ[c,p]]


Int[(c_.*F_[v_]^p_.)^q_,x_Symbol] :=
  Int[(c*F[ExpandToSum[v,x]]^p)^q,x] /;
FreeQ[{c,p,q},x] && TrigQ[F] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[x_^m_.*(c_.*F_[v_]^p_.)^q_,x_Symbol] :=
  Int[x^m*(c*F[ExpandToSum[v,x]]^p)^q,x] /;
FreeQ[{c,m,p,q},x] && TrigQ[F] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


(* ::Subsection::Closed:: *)
(*9.3 (d+e x)^m trig(a+b x+c x^2)^n*)


Int[Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Int[Sin[(b+2*c*x)^2/(4*c)],x] /;
FreeQ[{a,b,c},x] && ZeroQ[b^2-4*a*c]


Int[Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Int[Cos[(b+2*c*x)^2/(4*c)],x] /;
FreeQ[{a,b,c},x] && ZeroQ[b^2-4*a*c]


Int[Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Cos[(b^2-4*a*c)/(4*c)]*Int[Sin[(b+2*c*x)^2/(4*c)],x] - 
  Sin[(b^2-4*a*c)/(4*c)]*Int[Cos[(b+2*c*x)^2/(4*c)],x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]


Int[Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Cos[(b^2-4*a*c)/(4*c)]*Int[Cos[(b+2*c*x)^2/(4*c)],x] + 
  Sin[(b^2-4*a*c)/(4*c)]*Int[Sin[(b+2*c*x)^2/(4*c)],x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]


Int[Sin[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[Sin[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[Cos[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[Cos[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[Sin[v_]^n_.,x_Symbol] :=
  Int[Sin[ExpandToSum[v,x]]^n,x] /;
PositiveIntegerQ[n] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[Cos[v_]^n_.,x_Symbol] :=
  Int[Cos[ExpandToSum[v,x]]^n,x] /;
PositiveIntegerQ[n] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[(d_+e_.*x_)*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*Cos[a+b*x+c*x^2]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Sin[a+b*x+c*x^2]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[2*c*d-b*e]


Int[(d_.+e_.*x_)*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*Cos[a+b*x+c*x^2]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[2*c*d-b*e]


Int[(d_.+e_.*x_)*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Sin[a+b*x+c*x^2]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[2*c*d-b*e]


Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*(d+e*x)^(m-1)*Cos[a+b*x+c*x^2]/(2*c) + 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Sin[a+b*x+c*x^2]/(2*c) - 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*(d+e*x)^(m-1)*Cos[a+b*x+c*x^2]/(2*c) - 
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*Sin[a+b*x+c*x^2],x] + 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Sin[a+b*x+c*x^2]/(2*c) - 
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*Cos[a+b*x+c*x^2],x] - 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sin[a+b*x+c*x^2]/(e*(m+1)) -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Cos[a+b*x+c*x^2]/(e*(m+1)) + 
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sin[a+b*x+c*x^2]/(e*(m+1)) -
  (b*e-2*c*d)/(e^2*(m+1))*Int[(d+e*x)^(m+1)*Cos[a+b*x+c*x^2],x] -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Cos[a+b*x+c*x^2]/(e*(m+1)) + 
  (b*e-2*c*d)/(e^2*(m+1))*Int[(d+e*x)^(m+1)*Sin[a+b*x+c*x^2],x] +
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_.*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Defer[Int][(d+e*x)^m*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x]


Int[(d_.+e_.*x_)^m_.*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Defer[Int][(d+e*x)^m*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x]


Int[(d_.+e_.*x_)^m_.*Sin[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(d+e*x)^m,Sin[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[n] && n>1


Int[(d_.+e_.*x_)^m_.*Cos[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(d+e*x)^m,Cos[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[n] && n>1


Int[u_^m_.*Sin[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Sin[ExpandToSum[v,x]]^n,x] /;
FreeQ[m,x] && PositiveIntegerQ[n] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[u_^m_.*Cos[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Cos[ExpandToSum[v,x]]^n,x] /;
FreeQ[m,x] && PositiveIntegerQ[n] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[Tan[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][Tan[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,n},x]


Int[Cot[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][Cot[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,n},x]


Int[(d_+e_.*x_)*Tan[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*Log[Cos[a+b*x+c*x^2]]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)*Cot[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Log[Sin[a+b*x+c*x^2]]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[2*c*d-b*e]


Int[(d_.+e_.*x_)*Tan[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*Log[Cos[a+b*x+c*x^2]]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Tan[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[2*c*d-b*e]


Int[(d_.+e_.*x_)*Cot[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Log[Sin[a+b*x+c*x^2]]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Cot[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[2*c*d-b*e]


(* Int[x_^m_*Tan[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -x^(m-1)*Log[Cos[a+b*x+c*x^2]]/(2*c) - 
  b/(2*c)*Int[x^(m-1)*Tan[a+b*x+c*x^2],x] + 
  (m-1)/(2*c)*Int[x^(m-2)*Log[Cos[a+b*x+c*x^2]],x] /;
FreeQ[{a,b,c},x] && RationalQ[m] && m>1 *)


(* Int[x_^m_*Cot[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  x^(m-1)*Log[Sin[a+b*x+c*x^2]]/(2*c) -
  b/(2*c)*Int[x^(m-1)*Cot[a+b*x+c*x^2],x] -
  (m-1)/(2*c)*Int[x^(m-2)*Log[Sin[a+b*x+c*x^2]],x] /;
FreeQ[{a,b,c},x] && RationalQ[m] && m>1*)


Int[(d_.+e_.*x_)^m_.*Tan[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*Tan[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(d_.+e_.*x_)^m_.*Cot[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*Cot[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


(* ::Subsection::Closed:: *)
(*9.4 (e+f x)^m (a+b trig(c+d x)^n)^p*)


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^n*Int[(e+f*x)^m*Cos[-Pi*a/(4*b)+c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && IntegerQ[n]


(* Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^n*Int[(e+f*x)^m*Cos[-Pi/4*(1-a/b)+c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && IntegerQ[n] *)


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^n*Int[(e+f*x)^m*Cos[c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a-b] && IntegerQ[n]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^n*Int[(e+f*x)^m*Sin[c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a+b] && IntegerQ[n]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^(n-1/2)*Sqrt[a+b*Sin[c+d*x]]/Cos[-Pi*a/(4*b)+c/2+d*x/2]*Int[(e+f*x)^m*Cos[-Pi*a/(4*b)+c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[n]]


(* Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^(n-1/2)*Sqrt[a+b*Cos[c+d*x]]/Cos[-Pi/4*(1-a/b)+c/2+d*x/2]*Int[(e+f*x)^m*Cos[-Pi/4*(1-a/b)+c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[n]] *)


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^(n-1/2)*Sqrt[a+b*Cos[c+d*x]]/Cos[c/2+d*x/2]*Int[(e+f*x)^m*Cos[c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a-b] && Not[IntegerQ[n]]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
  (2*a)^(n-1/2)*Sqrt[a+b*Cos[c+d*x]]/Sin[c/2+d*x/2]*Int[(e+f*x)^m*Sin[c/2+d*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[a+b] && Not[IntegerQ[n]]


Int[x_/(a_+b_.*Sin[c_.+d_.*x_])^2,x_Symbol] :=
  a/(a^2-b^2)*Int[x/(a+b*Sin[c+d*x]),x] -
  b/(a^2-b^2)*Int[x*(b+a*Sin[c+d*x])/(a+b*Sin[c+d*x])^2,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[x_/(a_+b_.*Cos[c_.+d_.*x_])^2,x_Symbol] :=
  a/(a^2-b^2)*Int[x/(a+b*Cos[c+d*x]),x] -
  b/(a^2-b^2)*Int[x*(b+a*Cos[c+d*x])/(a+b*Cos[c+d*x])^2,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[x_^m_.*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2^n*Int[x^m*(I*b+2*a*E^(I*c+I*d*x)-I*b*E^(2*(I*c+I*d*x)))^n/E^(n*(I*c+I*d*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[n] && n<0


Int[x_^m_.*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
  1/2^n*Int[x^m*(b+2*a*E^(I*c+I*d*x)+b*E^(2*(I*c+I*d*x)))^n/E^(n*(I*c+I*d*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[n] && n<0


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sin[c_.+d_.*x_]*Cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(e+f*x)^m*(a+b*Sin[2*c+2*d*x]/2)^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[x_^m_.*(a_+b_.*Sin[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a+b-b*Cos[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b] && IntegersQ[m,n] && m>0 && n<0 && (n==-1 || m==1 && n==-2)


Int[x_^m_.*(a_+b_.*Cos[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a+b+b*Cos[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b] && IntegersQ[m,n] && m>0 && n<0 && (n==-1 || m==1 && n==-2)


(* ::Subsection::Closed:: *)
(*9.5 F^(c (a+b x)) trig(d+e x)^n*)


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_],x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]/(e^2+b^2*c^2*Log[F]^2) - 
  e*F^(c*(a+b*x))*Cos[d+e*x]/(e^2+b^2*c^2*Log[F]^2) /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2+b^2*c^2*Log[F]^2]


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_],x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]/(e^2+b^2*c^2*Log[F]^2) + 
  e*F^(c*(a+b*x))*Sin[d+e*x]/(e^2+b^2*c^2*Log[F]^2) /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2+b^2*c^2*Log[F]^2]


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^n/(e^2*n^2+b^2*c^2*Log[F]^2) - 
  e*n*F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n-1)/(e^2*n^2+b^2*c^2*Log[F]^2) + 
  (n*(n-1)*e^2)/(e^2*n^2+b^2*c^2*Log[F]^2)*Int[F^(c*(a+b*x))*Sin[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*n^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n>1


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^m_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^m/(e^2*m^2+b^2*c^2*Log[F]^2) + 
  e*m*F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(m-1)/(e^2*m^2+b^2*c^2*Log[F]^2) + 
  (m*(m-1)*e^2)/(e^2*m^2+b^2*c^2*Log[F]^2)*Int[F^(c*(a+b*x))*Cos[d+e*x]^(m-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*m^2+b^2*c^2*Log[F]^2] && RationalQ[m] && m>1


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) + 
  F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n+1)/(e*(n+1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && ZeroQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) - 
  F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(n+1)/(e*(n+1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && ZeroQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) + 
  F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n+1)/(e*(n+1)) + 
  (e^2*(n+2)^2+b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2))*Int[F^(c*(a+b*x))*Sin[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1 && n!=-2


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) - 
  F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(n+1)/(e*(n+1)) + 
  (e^2*(n+2)^2+b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2))*Int[F^(c*(a+b*x))*Cos[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1 && n!=-2


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
  E^(I*n*(d+e*x))*Sin[d+e*x]^n/(-1+E^(2*I*(d+e*x)))^n*Int[F^(c*(a+b*x))*(-1+E^(2*I*(d+e*x)))^n/E^(I*n*(d+e*x)),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
  E^(I*n*(d+e*x))*Cos[d+e*x]^n/(1+E^(2*I*(d+e*x)))^n*Int[F^(c*(a+b*x))*(1+E^(2*I*(d+e*x)))^n/E^(I*n*(d+e*x)),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Tan[d_.+e_.*x_]^n_.,x_Symbol] :=
  I^n*Int[ExpandIntegrand[F^(c*(a+b*x))*(1-E^(2*I*(d+e*x)))^n/(1+E^(2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Cot[d_.+e_.*x_]^n_.,x_Symbol] :=
  (-I)^n*Int[ExpandIntegrand[F^(c*(a+b*x))*(1+E^(2*I*(d+e*x)))^n/(1-E^(2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*(Sec[d+e x]^n/(e^2*n^2+b^2*c^2*Log[F]^2)) - 
  e*n*F^(c*(a+b*x))*Sec[d+e x]^(n+1)*(Sin[d+e x]/(e^2*n^2+b^2*c^2*Log[F]^2)) + 
  e^2*n*((n+1)/(e^2*n^2+b^2*c^2*Log[F]^2))*Int[F^(c*(a+b*x))*Sec[d+e x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*n^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*(Csc[d+e x]^n/(e^2*n^2+b^2*c^2*Log[F]^2)) + 
  e*n*F^(c*(a+b*x))*Csc[d+e x]^(n+1)*(Cos[d+e x]/(e^2*n^2+b^2*c^2*Log[F]^2)) + 
  e^2*n*((n+1)/(e^2*n^2+b^2*c^2*Log[F]^2))*Int[F^(c*(a+b*x))*Csc[d+e x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[e^2*n^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sec[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Sec[d+e x]^(n-1)*Sin[d+e x]/(e*(n-1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && ZeroQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2] && NonzeroQ[n-1] && NonzeroQ[n-2]


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Csc[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Csc[d+e x]^(n-1)*Cos[d+e x]/(e*(n-1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && ZeroQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2] && NonzeroQ[n-1] && NonzeroQ[n-2]


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sec[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Sec[d+e x]^(n-1)*Sin[d+e x]/(e*(n-1)) + 
  (e^2*(n-2)^2+b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2))*Int[F^(c*(a+b*x))*Sec[d+e x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2] && RationalQ[n] && n>1 && n!=2


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Csc[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) - 
  F^(c*(a+b*x))*Csc[d+e x]^(n-1)*Cos[d+e x]/(e*(n-1)) + 
  (e^2*(n-2)^2+b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2))*Int[F^(c*(a+b*x))*Csc[d+e x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2] && RationalQ[n] && n>1 && n!=2


(* Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(I*n*(d+e*x))/(1+E^(2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n] *)


(* Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_.,x_Symbol] :=
  (2*I)^n*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-I*n*(d+e*x))/(1-E^(-2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n] *)


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*E^(I*n*(d+e*x))*F^(c*(a+b*x))/(I*e*n+b*c*Log[F])*Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),-E^(2*I*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_.,x_Symbol] :=
  (-2*I)^n*E^(I*n*(d+e*x))*(F^(c*(a+b*x))/(I*e*n+b*c*Log[F]))*Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),E^(2*I*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_.,x_Symbol] :=
  (1+E^(2*I*(d+e*x)))^n*Sec[d+e*x]^n/E^(I*n*(d+e*x))*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(I*n*(d+e*x))/(1+E^(2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_.,x_Symbol] :=
  (1-E^(-2*I*(d+e*x)))^n*Csc[d+e*x]^n/E^(-I*n*(d+e*x))*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-I*n*(d+e*x))/(1-E^(-2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*f^n*Int[F^(c*(a+b*x))*Cos[d/2+e*x/2-f*Pi/(4*g)]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f^2-g^2] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*f^n*Int[F^(c*(a+b*x))*Cos[d/2+e*x/2]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f-g] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*f^n*Int[F^(c*(a+b*x))*Sin[d/2+e*x/2]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f+g] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^m_.*(f_+g_.*Sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  g^n*Int[F^(c*(a+b*x))*Tan[f*Pi/(4*g)-d/2-e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f^2-g^2] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
  f^n*Int[F^(c*(a+b*x))*Tan[d/2+e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f-g] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
  f^n*Int[F^(c*(a+b*x))*Cot[d/2+e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[f+g] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Cos[d_.+e_.*x_])/(f_+g_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  2*i*Int[F^(c*(a+b*x))*(Cos[d+e*x]/(f+g*Sin[d+e*x])),x] + 
  Int[F^(c*(a+b*x))*((h-i*Cos[d+e*x])/(f+g*Sin[d+e*x])),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && ZeroQ[f^2-g^2] && ZeroQ[h^2-i^2] && ZeroQ[g*h-f*i]


Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Sin[d_.+e_.*x_])/(f_+g_.*Cos[d_.+e_.*x_]),x_Symbol] :=
  2*i*Int[F^(c*(a+b*x))*(Sin[d+e*x]/(f+g*Cos[d+e*x])),x] + 
  Int[F^(c*(a+b*x))*((h-i*Sin[d+e*x])/(f+g*Cos[d+e*x])),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && ZeroQ[f^2-g^2] && ZeroQ[h^2-i^2] && ZeroQ[g*h+f*i]


Int[F_^(c_.*u_)*G_[v_]^n_.,x_Symbol] :=
  Int[F^(c*ExpandToSum[u,x])*G[ExpandToSum[v,x]]^n,x] /;
FreeQ[{F,c,n},x] && TrigQ[G] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[x_^m_.*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_.,x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[F^(c*(a+b*x))*Sin[d+e*x]^n,x]]},
  Dist[x^m,u,x] - m*Int[x^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e},x] && RationalQ[m] && m>0 && PositiveIntegerQ[n]


Int[x_^m_.*F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_.,x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[F^(c*(a+b*x))*Cos[d+e*x]^n,x]]},
  Dist[x^m,u,x] - m*Int[x^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e},x] && RationalQ[m] && m>0 && PositiveIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*Cos[f_.+g_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[F^(c*(a+b*x)),Sin[d+e*x]^m*Cos[f+g*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && PositiveIntegerQ[m,n]


Int[x_^p_.*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*Cos[f_.+g_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^p*F^(c*(a+b*x)),Sin[d+e*x]^m*Cos[f+g*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && PositiveIntegerQ[m,n,p]


Int[F_^(c_.*(a_.+b_.*x_))*G_[d_.+e_.*x_]^m_.*H_[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^(c*(a+b*x)),G[d+e*x]^m*H[d+e*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && PositiveIntegerQ[m,n] && TrigQ[G] && TrigQ[H]


Int[F_^u_*Sin[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Sin[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || QuadraticQ[u,x]) && (LinearQ[v,x] || QuadraticQ[v,x]) && PositiveIntegerQ[n]


Int[F_^u_*Cos[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Cos[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || QuadraticQ[u,x]) && (LinearQ[v,x] || QuadraticQ[v,x]) && PositiveIntegerQ[n]


Int[F_^u_*Sin[v_]^m_.*Cos[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Sin[v]^m*Cos[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || QuadraticQ[u,x]) && (LinearQ[v,x] || QuadraticQ[v,x]) && PositiveIntegerQ[m,n]


(* ::Subsection::Closed:: *)
(*9.6 x^m trig(a+b log(c x^n))^p*)


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(p+2)*Sin[a+b*Log[c*x^n]]^(p+2)/(p+1) + 
  x*Cot[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[b^2*n^2*(p+2)^2+1] && NonzeroQ[p+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(p+2)*Cos[a+b*Log[c*x^n]]^(p+2)/(p+1) - 
  x*Tan[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[b^2*n^2*(p+2)^2+1] && NonzeroQ[p+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(E^(a*b*n*p)/(2*b*n*p)*(c*x^n)^(-1/(n*p))-E^(-a*b*n*p)/(2*b*n*p)*(c*x^n)^(1/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[p] && ZeroQ[b^2*n^2*p^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(E^(a*b*n*p)/2*(c*x^n)^(-1/(n*p))-E^(-a*b*n*p)/2*(c*x^n)^(1/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[p] && ZeroQ[b^2*n^2*p^2+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  x*Sin[a+b*Log[c*x^n]]/(b^2*n^2+1) -
  b*n*x*Cos[a+b*Log[c*x^n]]/(b^2*n^2+1) /;
FreeQ[{a,b,c,n},x] && NonzeroQ[b^2*n^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  x*Cos[a+b*Log[c*x^n]]/(1+b^2*n^2) +
  b*n*x*Sin[a+b*Log[c*x^n]]/(b^2*n^2+1) /;
FreeQ[{a,b,c,n},x] && NonzeroQ[b^2*n^2+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Sin[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) -
  b*n*p*x*Cos[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2+1) +
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2+1)*Int[Sin[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && NonzeroQ[b^2*n^2*p^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Cos[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) +
  b*n*p*x*Cos[a+b*Log[c*x^n]]^(p-1)*Sin[a+b*Log[c*x^n]]/(b^2*n^2*p^2+1) +
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2+1)*Int[Cos[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && NonzeroQ[b^2*n^2*p^2+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Cot[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  x*Sin[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2+1)/(b^2*n^2*(p+1)*(p+2))*Int[Sin[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[b^2*n^2*(p+2)^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*Tan[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  x*Cos[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2+1)/(b^2*n^2*(p+1)*(p+2))*Int[Cos[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[b^2*n^2*(p+2)^2+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(I/(E^(I*a)*(c*x^n)^(I*b))-I*E^(I*a)*(c*x^n)^(I*b))^p/((1-I*b*n*p)*(2-2*E^(2*I*a)*(c*x^n)^(2*I*b))^p)*
    Hypergeometric2F1[-p,(1-I*b*n*p)/(2*I*b*n),1+(1-I*b*n*p)/(2*I*b*n),E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[b^2*n^2*p^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(1/(E^(I*a)*(c*x^n)^(I*b))+E^(I*a)*(c*x^n)^(I*b))^p/((1-I*b*n*p)*(2+2*E^(2*I*a)*(c*x^n)^(2*I*b))^p)*
    Hypergeometric2F1[-p,(1-I*b*n*p)/(2*I*b*n),1+(1-I*b*n*p)/(2*I*b*n),-E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[b^2*n^2*p^2+1]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p+2)*x^(m+1)*Sin[a+b*Log[c*x^n]]^(p+2)/((m+1)*(p+1)) + 
  x^(m+1)*Cot[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[b^2*n^2*(p+2)^2+(m+1)^2] && NonzeroQ[p+1] && NonzeroQ[m+1]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p+2)*x^(m+1)*Cos[a+b*Log[c*x^n]]^(p+2)/((m+1)*(p+1)) - 
  x^(m+1)*Tan[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[b^2*n^2*(p+2)^2+(m+1)^2] && NonzeroQ[p+1] && NonzeroQ[m+1]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  1/2^p*Int[ExpandIntegrand[x^m*((m+1)/(b*n*p)*E^(a*b*n*p/(m+1))*(c*x^n)^(-(m+1)/(n*p)) - 
    (m+1)/(b*n*p)*E^(-a*b*n*p/(m+1))*(c*x^n)^((m+1)/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p] && ZeroQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  1/2^p*Int[ExpandIntegrand[x^m*(E^(a*b*n*p/(m+1))*(c*x^n)^(-(m+1)/(n*p)) - 
    E^(-a*b*n*p/(m+1))*(c*x^n)^((m+1)/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p] && ZeroQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  (m+1)*x^(m+1)*Sin[a+b*Log[c*x^n]]/(b^2*n^2+(m+1)^2) -
  b*n*x^(m+1)*Cos[a+b*Log[c*x^n]]/(b^2*n^2+(m+1)^2) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2*n^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  (m+1)*x^(m+1)*Cos[a+b*Log[c*x^n]]/(b^2*n^2+(m+1)^2) +
  b*n*x^(m+1)*Sin[a+b*Log[c*x^n]]/(b^2*n^2+(m+1)^2) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2*n^2+(m+1)^2]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (m+1)*x^(m+1)*Sin[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) -
  b*n*p*x^(m+1)*Cos[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2+(m+1)^2) +
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2+(m+1)^2)*Int[x^m*Sin[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && NonzeroQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (m+1)*x^(m+1)*Cos[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) +
  b*n*p*x^(m+1)*Sin[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2+(m+1)^2) +
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2+(m+1)^2)*Int[x^m*Cos[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && NonzeroQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*Cot[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  (m+1)*x^(m+1)*Sin[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2+(m+1)^2)/(b^2*n^2*(p+1)*(p+2))*Int[x^m*Sin[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[b^2*n^2*(p+2)^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x^(m+1)*Tan[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  (m+1)*x^(m+1)*Cos[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2+(m+1)^2)/(b^2*n^2*(p+1)*(p+2))*Int[x^m*Cos[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[b^2*n^2*(p+2)^2+(m+1)^2]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*(I*E^(-I*a)*(c*x^n)^(-I*b)-I*E^(I*a)*(c*x^n)^(I*b))^p/((m+1-I*b*n*p)*(2-2*E^(2*I*a)*(c*x^n)^(2*I*b))^p)*
    Hypergeometric2F1[-p,(m+1-I*b*n*p)/(2*I*b*n),1+(m+1-I*b*n*p)/(2*I*b*n),E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*(E^(-I*a)*(c*x^n)^(-I*b)+E^(I*a)*(c*x^n)^(I*b))^p/((m+1-I*b*n*p)*(2+2*E^(2*I*a)*(c*x^n)^(2*I*b))^p)*
    Hypergeometric2F1[-p,(m+1-I*b*n*p)/(2*I*b*n),1+(m+1-I*b*n*p)/(2*I*b*n),-E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[b^2*n^2*p^2+(m+1)^2]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*E^(a*b*n)*Int[(c*x^n)^(1/n)/(E^(2*a*b*n)+(c*x^n)^(2/n)),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[b^2*n^2+1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*b*n*E^(a*b*n)*Int[(c*x^n)^(1/n)/(E^(2*a*b*n)-(c*x^n)^(2/n)),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[b^2*n^2+1]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x*Sec[a+b*Log[c*x^n]]^(p-2)/(p-1) + 
  x*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[b^2*n^2*(p-2)^2+1] && NonzeroQ[p-1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x*Csc[a+b*Log[c*x^n]]^(p-2)/(p-1) - 
  x*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[b^2*n^2*(p-2)^2+1] && NonzeroQ[p-1]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Sec[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2+1)/(b^2*n^2*(p-1)*(p-2))*Int[Sec[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2+1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Csc[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2+1)/(b^2*n^2*(p-1)*(p-2))*Int[Csc[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2+1]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -b*n*p*x*Sin[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+1) +
  x*Sec[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2+1)*Int[Sec[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2+1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  b*n*p*x*Cos[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+1) +
  x*Csc[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2+1)*Int[Csc[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2+1]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x*(2+2*E^(2*I*a)*(c*x^n)^(2*I*b))^p/(1+I*b*n*p)*
    (E^(I*a)*(c*x^n)^(I*b)/(1+E^(2*I*a)*(c*x^n)^(2*I*b)))^p*
    Hypergeometric2F1[p,(1+I*b*n*p)/(2*I*b*n),1+(1+I*b*n*p)/(2*I*b*n),-E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[b^2*n^2*p^2+1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x*(2-2*E^(2*I*a)*(c*x^n)^(2*I*b))^p/(1+I*b*n*p)*
    (-I*E^(I*a)*(c*x^n)^(I*b)/(1-E^(2*I*a)*(c*x^n)^(2*I*b)))^p*
    Hypergeometric2F1[p,(1+I*b*n*p)/(2*I*b*n),1+(1+I*b*n*p)/(2*I*b*n),E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[b^2*n^2*p^2+1]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*E^(a*b*n/(m+1))*Int[x^m*(c*x^n)^((m+1)/n)/(E^(2*a*b*n/(m+1))+(c*x^n)^(2*(m+1)/n)),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[b^2*n^2+(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*b*n/(m+1)*E^(a*b*n/(m+1))*Int[x^m*(c*x^n)^((m+1)/n)/(E^(2*a*b*n/(m+1))-(c*x^n)^(2*(m+1)/n)),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[b^2*n^2+(m+1)^2]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x^(m+1)*Sec[a+b*Log[c*x^n]]^(p-2)/((m+1)*(p-1)) + 
  x^(m+1)*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[b^2*n^2*(p-2)^2+(m+1)^2] && NonzeroQ[m+1] && NonzeroQ[p-1]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x^(m+1)*Csc[a+b*Log[c*x^n]]^(p-2)/((m+1)*(p-1)) - 
  x^(m+1)*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[b^2*n^2*(p-2)^2+(m+1)^2] && NonzeroQ[m+1] && NonzeroQ[p-1]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  (m+1)*x^(m+1)*Sec[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2+(m+1)^2)/(b^2*n^2*(p-1)*(p-2))*Int[x^m*Sec[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2+(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x^(m+1)*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  (m+1)*x^(m+1)*Csc[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2+(m+1)^2)/(b^2*n^2*(p-1)*(p-2))*Int[x^m*Csc[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2+(m+1)^2]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -b*n*p*x^(m+1)*Sin[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+(m+1)^2) +
  (m+1)*x^(m+1)*Sec[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2+(m+1)^2)*Int[x^m*Sec[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  b*n*p*x^(m+1)*Cos[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+(m+1)^2) +
  (m+1)*x^(m+1)*Csc[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2+(m+1)^2)*Int[x^m*Csc[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x^(m+1)*(2+2*E^(2*I*a)*(c*x^n)^(2*I*b))^p/(m+1+I*b*n*p)*
    (E^(I*a)*(c*x^n)^(I*b)/(1+E^(2*I*a)*(c*x^n)^(2*I*b)))^p*
    Hypergeometric2F1[p,(m+1+I*b*n*p)/(2*I*b*n),1+(m+1+I*b*n*p)/(2*I*b*n),-E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x^(m+1)*(2-2*E^(2*I*a)*(c*x^n)^(2*I*b))^p/(m+1+I*b*n*p)*
    (-I*E^(I*a)*(c*x^n)^(I*b)/(1-E^(2*I*a)*(c*x^n)^(2*I*b)))^p*
    Hypergeometric2F1[p,(m+1+I*b*n*p)/(2*I*b*n),1+(m+1+I*b*n*p)/(2*I*b*n),E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[b^2*n^2*p^2+(m+1)^2]


Int[Sin[a_.*x_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -Cos[a*x*Log[b*x]^p]/a -
  p*Int[Sin[a*x*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b},x] && RationalQ[p] && p>0


Int[Cos[a_.*x_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sin[a*x*Log[b*x]^p]/a -
  p*Int[Cos[a*x*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b},x] && RationalQ[p] && p>0


Int[Sin[a_.*x_^n_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -Cos[a*x^n*Log[b*x]^p]/(a*n*x^(n-1)) -
  p/n*Int[Sin[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] -
  (n-1)/(a*n)*Int[Cos[a*x^n*Log[b*x]^p]/x^n,x] /;
FreeQ[{a,b},x] && RationalQ[n,p] && p>0


Int[Cos[a_.*x_^n_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sin[a*x^n*Log[b*x]^p]/(a*n*x^(n-1)) -
  p/n*Int[Cos[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] +
  (n-1)/(a*n)*Int[Sin[a*x^n*Log[b*x]^p]/x^n,x] /;
FreeQ[{a,b},x] && RationalQ[n,p] && p>0


Int[x_^m_.*Sin[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -Cos[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Sin[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-n+1] && RationalQ[p] && p>0


Int[x_^m_.*Cos[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sin[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Cos[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-n+1] && RationalQ[p] && p>0


Int[x_^m_.*Sin[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -x^(m-n+1)*Cos[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Sin[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] +
  (m-n+1)/(a*n)*Int[x^(m-n)*Cos[a*x^n*Log[b*x]^p],x] /;
FreeQ[{a,b,m,n},x] && RationalQ[p] && p>0 && NonzeroQ[m-n+1]


Int[x_^m_*Cos[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  x^(m-n+1)*Sin[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Cos[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] -
  (m-n+1)/(a*n)*Int[x^(m-n)*Sin[a*x^n*Log[b*x]^p],x] /;
FreeQ[{a,b,m,n},x] && RationalQ[p] && p>0 && NonzeroQ[m-n+1]


(* ::Subsection::Closed:: *)
(*9.7 Active Trig Functions Rules*)


Int[Sin[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Sin[a*x]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[n]


Int[Cos[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Cos[a*x]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[n]


Int[Sin[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Sin[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n] && NonzeroQ[b*c-a*d]


Int[Cos[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Cos[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n] && NonzeroQ[b*c-a*d]


Int[Sin[u_]^n_.,x_Symbol] :=
  Module[{lst=QuotientOfLinearsParts[u,x]},
  Int[Sin[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
PositiveIntegerQ[n] && QuotientOfLinearsQ[u,x]


Int[Cos[u_]^n_.,x_Symbol] :=
  Module[{lst=QuotientOfLinearsParts[u,x]},
  Int[Cos[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
PositiveIntegerQ[n] && QuotientOfLinearsQ[u,x]


Int[u_.*Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
  Int[u*Sin[v]^(p+q),x] /;
ZeroQ[v-w]


Int[u_.*Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[u*Cos[v]^(p+q),x] /;
ZeroQ[v-w]


Int[Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Sin[v]^p*Sin[w]^q,x],x] /;
(PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x]) && PositiveIntegerQ[p,q]


Int[Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Cos[v]^p*Cos[w]^q,x],x] /;
(PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x]) && PositiveIntegerQ[p,q]


Int[x_^m_.*Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sin[v]^p*Sin[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Cos[v]^p*Cos[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[u_.*Sin[v_]^p_.*Cos[w_]^p_.,x_Symbol] :=
  1/2^p*Int[u*Sin[2*v]^p,x] /;
ZeroQ[v-w] && IntegerQ[p]


Int[Sin[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Sin[v]^p*Cos[w]^q,x],x] /;
PositiveIntegerQ[p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Sin[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sin[v]^p*Cos[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[Sin[v_]*Tan[w_]^n_.,x_Symbol] :=
  -Int[Cos[v]*Tan[w]^(n-1),x] + Cos[v-w]*Int[Sec[w]*Tan[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Cos[v_]*Cot[w_]^n_.,x_Symbol] :=
  -Int[Sin[v]*Cot[w]^(n-1),x] + Cos[v-w]*Int[Csc[w]*Cot[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Sin[v_]*Cot[w_]^n_.,x_Symbol] :=
  Int[Cos[v]*Cot[w]^(n-1),x] + Sin[v-w]*Int[Csc[w]*Cot[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Cos[v_]*Tan[w_]^n_.,x_Symbol] :=
  Int[Sin[v]*Tan[w]^(n-1),x] - Sin[v-w]*Int[Sec[w]*Tan[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Sin[v_]*Sec[w_]^n_.,x_Symbol] :=
  Cos[v-w]*Int[Tan[w]*Sec[w]^(n-1),x] + Sin[v-w]*Int[Sec[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Cos[v_]*Csc[w_]^n_.,x_Symbol] :=
  Cos[v-w]*Int[Cot[w]*Csc[w]^(n-1),x] - Sin[v-w]*Int[Csc[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Sin[v_]*Csc[w_]^n_.,x_Symbol] :=
  Sin[v-w]*Int[Cot[w]*Csc[w]^(n-1),x] + Cos[v-w]*Int[Csc[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[Cos[v_]*Sec[w_]^n_.,x_Symbol] :=
  -Sin[v-w]*Int[Tan[w]*Sec[w]^(n-1),x] + Cos[v-w]*Int[Sec[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]


Int[x_^m_.*Sin[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d*Subst[Int[(-c/d+x/d)^m*Sin[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && RationalQ[p]


Int[x_^m_.*Cos[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d*Subst[Int[(-c/d+x/d)^m*Cos[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && RationalQ[p]


Int[x_^m_./(a_.+b_.*Cos[d_.+e_.*x_]^2+c_.*Sin[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[x^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[m] && NonzeroQ[a+b] && NonzeroQ[a+c]


Int[x_^m_.*Sec[d_.+e_.*x_]^2/(b_+c_.*Tan[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[x^m/(b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{b,c,d,e},x] && PositiveIntegerQ[m]


Int[x_^m_.*Sec[d_.+e_.*x_]^2/(b_.+a_.*Sec[d_.+e_.*x_]^2+c_.*Tan[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[x^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[m] && NonzeroQ[a+b] && NonzeroQ[a+c]


Int[x_^m_.*Csc[d_.+e_.*x_]^2/(c_+b_.*Cot[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[x^m/(b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{b,c,d,e},x] && PositiveIntegerQ[m]


Int[x_^m_.*Csc[d_.+e_.*x_]^2/(c_.+b_.*Cot[d_.+e_.*x_]^2+a_.*Csc[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[x^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[m] && NonzeroQ[a+b] && NonzeroQ[a+c]


Int[x_^m_.*Cos[c_.+d_.*x_]/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  -I*x^(m+1)/(b*(m+1)) + 
  Int[x^m*E^(I*(c+d*x))/(a-Sqrt[a^2-b^2]-I*b*E^(I*(c+d*x))),x] + 
  Int[x^m*E^(I*(c+d*x))/(a+Sqrt[a^2-b^2]-I*b*E^(I*(c+d*x))),x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_.*Sin[c_.+d_.*x_]/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
  I*x^(m+1)/(b*(m+1)) - 
  I*Int[x^m*E^(I*(c+d*x))/(a-Sqrt[a^2-b^2]+b*E^(I*(c+d*x))),x] - 
  I*Int[x^m*E^(I*(c+d*x))/(a+Sqrt[a^2-b^2]+b*E^(I*(c+d*x))),x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_.*Cos[c_.+d_.*x_]^n_/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  a/b^2*Int[x^m*Cos[c+d*x]^(n-2),x] - 
  1/b*Int[x^m*Cos[c+d*x]^(n-2)*Sin[c+d*x],x] - 
  (a^2-b^2)/b^2*Int[x^m*Cos[c+d*x]^(n-2)/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1


Int[x_^m_.*Sin[c_.+d_.*x_]^n_/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
  a/b^2*Int[x^m*Sin[c+d*x]^(n-2),x] - 
  1/b*Int[x^m*Sin[c+d*x]^(n-2)*Cos[c+d*x],x] - 
  (a^2-b^2)/b^2*Int[x^m*Sin[c+d*x]^(n-2)/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1


Int[x_*(A_+B_.*Sin[c_.+d_.*x_])/(a_+b_.*Sin[c_.+d_.*x_])^2,x_Symbol] :=
  -B*x*Cos[c+d*x]/(a*d*(a+b*Sin[c+d*x])) +
  B/(a*d)*Int[Cos[c+d*x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a*A-b*B]


Int[x_*(A_+B_.*Cos[c_.+d_.*x_])/(a_+b_.*Cos[c_.+d_.*x_])^2,x_Symbol] :=
  B*x*Sin[c+d*x]/(a*d*(a+b*Cos[c+d*x])) -
  B/(a*d)*Int[Sin[c+d*x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a*A-b*B]


Int[Sec[v_]^m_.*(a_+b_.*Tan[v_])^n_., x_Symbol] :=
  Int[(a*Cos[v]+b*Sin[v])^n,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m+n==0 && OddQ[m]


Int[Csc[v_]^m_.*(a_+b_.*Cot[v_])^n_., x_Symbol] :=
  Int[(b*Cos[v]+a*Sin[v])^n,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m+n==0 && OddQ[m]


Int[u_.*Sin[a_.+b_.*x_]^m_.*Sin[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[u,Sin[a+b*x]^m*Sin[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m,n]


Int[u_.*Cos[a_.+b_.*x_]^m_.*Cos[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[u,Cos[a+b*x]^m*Cos[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m,n]


Int[Sec[a_.+b_.*x_]*Sec[c_+d_.*x_],x_Symbol] :=
  -Csc[(b*c-a*d)/d]*Int[Tan[a+b*x],x] + Csc[(b*c-a*d)/b]*Int[Tan[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b^2-d^2] && NonzeroQ[b*c-a*d]


Int[Csc[a_.+b_.*x_]*Csc[c_+d_.*x_],x_Symbol] :=
  Csc[(b*c-a*d)/b]*Int[Cot[a+b*x],x] - Csc[(b*c-a*d)/d]*Int[Cot[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b^2-d^2] && NonzeroQ[b*c-a*d]


Int[Tan[a_.+b_.*x_]*Tan[c_+d_.*x_],x_Symbol] :=
  -b*x/d + b/d*Cos[(b*c-a*d)/d]*Int[Sec[a+b*x]*Sec[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b^2-d^2] && NonzeroQ[b*c-a*d]


Int[Cot[a_.+b_.*x_]*Cot[c_+d_.*x_],x_Symbol] :=
  -b*x/d + Cos[(b*c-a*d)/d]*Int[Csc[a+b*x]*Csc[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b^2-d^2] && NonzeroQ[b*c-a*d]


Int[ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tan[a+b*x]] - 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c+I*d)^2+1]


Int[ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tan[a+b*x]] + 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c+I*d)^2+1]


Int[ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tan[a+b*x]] - 
  b*(I+c+I*d)*Int[x/(I+c+I*d+(I+c-I*d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(-I+c+I*d)*Int[x/(-I+c+I*d+(-I+c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c+I*d)^2+1]


Int[ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tan[a+b*x]] + 
  b*(I+c+I*d)*Int[x/(I+c+I*d+(I+c-I*d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(-I+c+I*d)*Int[x/(-I+c+I*d+(-I+c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c+I*d)^2+1]


Int[x_^m_.*ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTan[c+d*Tan[a+b*x]]/(m+1) - 
  I*b/(m+1)*Int[x^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c+I*d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCot[c+d*Tan[a+b*x]]/(m+1) + 
  I*b/(m+1)*Int[x^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c+I*d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTan[c+d*Tan[a+b*x]]/(m+1) - 
  b*(I+c+I*d)/(m+1)*Int[x^(m+1)/(I+c+I*d+(I+c-I*d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(-I+c+I*d)/(m+1)*Int[x^(m+1)/(-I+c+I*d+(-I+c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c+I*d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCot[c+d*Tan[a+b*x]]/(m+1) + 
  b*(I+c+I*d)/(m+1)*Int[x^(m+1)/(I+c+I*d+(I+c-I*d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(-I+c+I*d)/(m+1)*Int[x^(m+1)/(-I+c+I*d+(-I+c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c+I*d)^2+1] && RationalQ[m] && m>0


Int[ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Cot[a+b*x]] - 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-I*d)^2+1]


Int[ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Cot[a+b*x]] + 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-I*d)^2+1]


Int[ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Cot[a+b*x]] + 
  b*(I-c+I*d)*Int[x/(I-c+I*d+(-I+c+I*d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(I+c-I*d)*Int[x/(-I-c+I*d+(I+c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-I*d)^2+1]


Int[ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Cot[a+b*x]] - 
  b*(I-c+I*d)*Int[x/(I-c+I*d+(-I+c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(I+c-I*d)*Int[x/(-I-c+I*d+(I+c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-I*d)^2+1]


Int[x_^m_.*ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTan[c+d*Cot[a+b*x]]/(m+1) - 
  I*b/(m+1)*Int[x^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-I*d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCot[c+d*Cot[a+b*x]]/(m+1) + 
  I*b/(m+1)*Int[x^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-I*d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTan[c+d*Cot[a+b*x]]/(m+1) + 
  b*(I-c+I*d)/(m+1)*Int[x^(m+1)/(I-c+I*d+(-I+c+I*d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(I+c-I*d)/(m+1)*Int[x^(m+1)/(-I-c+I*d+(I+c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-I*d)^2+1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCot[c+d*Cot[a+b*x]]/(m+1) - 
  b*(I-c+I*d)/(m+1)*Int[x^(m+1)/(I-c+I*d+(-I+c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(I+c-I*d)/(m+1)*Int[x^(m+1)/(-I-c+I*d+(I+c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-I*d)^2+1] && RationalQ[m] && m>0


Int[ArcTanh[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Tan[a+b*x]] + 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c+I*d)^2-1]


Int[ArcCoth[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Tan[a+b*x]] + 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c+I*d)^2-1]


Int[ArcTanh[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Tan[a+b*x]] + 
  I*b*(1+c+I*d)*Int[x/(1+c+I*d+(1+c-I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1-c-I*d)*Int[x/(1-c-I*d+(1-c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c+I*d)^2-1]


Int[ArcCoth[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Tan[a+b*x]] + 
  I*b*(1+c+I*d)*Int[x/(1+c+I*d+(1+c-I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1-c-I*d)*Int[x/(1-c-I*d+(1-c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c+I*d)^2-1]


Int[x_^m_.*ArcTanh[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTanh[c+d*Tan[a+b*x]]/(m+1) + 
  I*b/(m+1)*Int[x^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c+I*d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCoth[c+d*Tan[a+b*x]]/(m+1) + 
  I*b/(m+1)*Int[x^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c+I*d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcTanh[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTanh[c+d*Tan[a+b*x]]/(m+1) + 
  I*b*(1+c+I*d)/(m+1)*Int[x^(m+1)/(1+c+I*d+(1+c-I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1-c-I*d)/(m+1)*Int[x^(m+1)/(1-c-I*d+(1-c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c+I*d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCoth[c+d*Tan[a+b*x]]/(m+1) + 
  I*b*(1+c+I*d)/(m+1)*Int[x^(m+1)/(1+c+I*d+(1+c-I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1-c-I*d)/(m+1)*Int[x^(m+1)/(1-c-I*d+(1-c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c+I*d)^2-1] && RationalQ[m] && m>0


Int[ArcTanh[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Cot[a+b*x]] + 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-I*d)^2-1]


Int[ArcCoth[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Cot[a+b*x]] + 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-I*d)^2-1]


Int[ArcTanh[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Cot[a+b*x]] + 
  I*b*(1+c-I*d)*Int[x/(1+c-I*d-(1+c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1-c+I*d)*Int[x/(1-c+I*d-(1-c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-I*d)^2-1]


Int[ArcCoth[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Cot[a+b*x]] + 
  I*b*(1+c-I*d)*Int[x/(1+c-I*d-(1+c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1-c+I*d)*Int[x/(1-c+I*d-(1-c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-I*d)^2-1]


Int[x_^m_.*ArcTanh[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTanh[c+d*Cot[a+b*x]]/(m+1) + 
  I*b/(m+1)*Int[x^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-I*d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCoth[c+d*Cot[a+b*x]]/(m+1) + 
  I*b/(m+1)*Int[x^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[(c-I*d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcTanh[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcTanh[c+d*Cot[a+b*x]]/(m+1) + 
  I*b*(1+c-I*d)/(m+1)*Int[x^(m+1)/(1+c-I*d-(1+c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1-c+I*d)/(m+1)*Int[x^(m+1)/(1-c+I*d-(1-c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-I*d)^2-1] && RationalQ[m] && m>0


Int[x_^m_.*ArcCoth[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x^(m+1)*ArcCoth[c+d*Cot[a+b*x]]/(m+1) + 
  I*b*(1+c-I*d)/(m+1)*Int[x^(m+1)/(1+c-I*d-(1+c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1-c+I*d)/(m+1)*Int[x^(m+1)/(1-c+I*d-(1-c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[(c-I*d)^2-1] && RationalQ[m] && m>0


Int[u_.*(a_.*Cos[v_]+b_.*Sin[v_])^n_.,x_Symbol] :=
  Int[u*(a*E^(-a/b*v))^n,x] /;
FreeQ[{a,b,n},x] && ZeroQ[a^2+b^2]
