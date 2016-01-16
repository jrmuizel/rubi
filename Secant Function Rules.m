(* ::Package:: *)

(* ::Section:: *)
(*Secant Function Rules*)


(* ::Subsection::Closed:: *)
(*1 (c sec)^n*)


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


Int[(c_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c*Sin[a+b*x]*(c*Sec[a+b*x])^(n-1)/(b*(n-1)) + 
  c^2*(n-2)/(n-1)*Int[(c*Sec[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1 && Not[EvenQ[n]]


Int[(c_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  -c*Cos[a+b*x]*(c*Csc[a+b*x])^(n-1)/(b*(n-1)) + 
  c^2*(n-2)/(n-1)*Int[(c*Csc[a+b*x])^(n-2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1 && Not[EvenQ[n]]


(* Int[1/sec[a_.+b_.*x_],x_Symbol] :=
  Sin[a+b*x]/b /;
FreeQ[{a,b},x] *)


(* Int[1/csc[a_.+b_.*x_],x_Symbol] :=
  -Cos[a+b*x]/b /;
FreeQ[{a,b},x] *)


Int[(c_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  -Sin[a+b*x]*(c*Sec[a+b*x])^(n+1)/(b*c*n) + 
  (n+1)/(c^2*n)*Int[(c*Sec[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]*(c*Csc[a+b*x])^(n+1)/(b*c*n) + 
  (n+1)/(c^2*n)*Int[(c*Csc[a+b*x])^(n+2),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(c_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  Cos[a+b*x]^n*(c*Sec[a+b*x])^n*Int[1/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && ZeroQ[n^2-1/4]


Int[(c_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  Sin[a+b*x]^n*(c*Csc[a+b*x])^n*Int[1/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && ZeroQ[n^2-1/4]


Int[(c_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  1/c*Cos[a+b*x]^(n+1)*(c*Sec[a+b*x])^(n+1)*Int[1/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[2*n]] && RationalQ[n] && n<0


Int[(c_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  1/c*Sin[a+b*x]^(n+1)*(c*Csc[a+b*x])^(n+1)*Int[1/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[2*n]] && RationalQ[n] && n<0


Int[(c_.*sec[a_.+b_.*x_])^n_,x_Symbol] :=
  c*Cos[a+b*x]^(n-1)*(c*Sec[a+b*x])^(n-1)*Int[1/Cos[a+b*x]^n,x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[2*n]] && Not[RationalQ[n] && n<0]


Int[(c_.*csc[a_.+b_.*x_])^n_,x_Symbol] :=
  c*Sin[a+b*x]^(n-1)*(c*Csc[a+b*x])^(n-1)*Int[1/Sin[a+b*x]^n,x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[2*n]] && Not[RationalQ[n] && n<0]


(* ::Subsection::Closed:: *)
(*2 (a+b sec)^n*)


Int[(a_+b_.*sec[c_.+d_.*x_])^2,x_Symbol] :=
  a^2*x + 2*a*b*Int[Sec[c+d*x],x] + b^2*Int[Sec[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*csc[c_.+d_.*x_])^2,x_Symbol] :=
  a^2*x + 2*a*b*Int[Csc[c+d*x],x] + b^2*Int[Csc[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x]


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  2*b/d*Subst[Int[1/(a+x^2),x],x,b*Tan[c+d*x]/Sqrt[a+b*Sec[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*b/d*Subst[Int[1/(a+x^2),x],x,b*Cot[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n-2)/(d*(n-1)) + 
  a/(n-1)*Int[(a*(n-1)+b*(3*n-4)*Sec[c+d*x])*(a+b*Sec[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-2)/(d*(n-1)) + 
  a/(n-1)*Int[(a*(n-1)+b*(3*n-4)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


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
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[(a*(2*n+1)-b*(n+1)*Csc[c+d*x])*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  2*a*(a+b*Sec[c+d*x])^n*Tan[(c+d*x)/2]*(1-Tan[(c+d*x)/2]^2)^n/(d*(a+n*(a-b)))*
    AppellF1[n*(a-b)/(2*a)+1/2,n,1,n*(a-b)/(2*a)+3/2,Tan[(c+d*x)/2]^2,-Tan[(c+d*x)/2]^2] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -2*a*(a+b*Csc[c+d*x])^n*Cot[(c+d*x)/2+Pi/4]*(1-Cot[(c+d*x)/2+Pi/4]^2)^n/(d*(a+n*(a-b)))*
    AppellF1[n*(a-b)/(2*a)+1/2,n,1,n*(a-b)/(2*a)+3/2,Cot[(c+d*x)/2+Pi/4]^2,-Cot[(c+d*x)/2+Pi/4]^2] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  a*Int[1/Sqrt[a+b*Sec[c+d*x]],x] + b*Int[Sec[c+d*x]/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  a*Int[1/Sqrt[a+b*Csc[c+d*x]],x] + b*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[c_.+d_.*x_])^(3/2),x_Symbol] :=
  Int[(a^2+b*(2*a-b)*Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] + 
  b^2*Int[Sec[c+d*x]*(1+Sec[c+d*x])/Sqrt[a+b*Sec[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  Int[(a^2+b*(2*a-b)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  b^2*Int[Csc[c+d*x]*(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
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
  x/a - 1/a*Int[1/(1+a/b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  x/a - 1/a*Int[1/(1+a/b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*sec[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[b+a*Cos[c+d*x]]/(Sqrt[Cos[c+d*x]]*Sqrt[a+b*Sec[c+d*x]])*Int[Sqrt[Cos[c+d*x]]/Sqrt[b+a*Cos[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]])*Int[Sqrt[Sin[c+d*x]]/Sqrt[b+a*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Tan[c+d*x]*(a+b*Sec[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[(a^2-b^2)*(n+1)-a*b*(n+1)*Sec[c+d*x]+b^2*(n+2)*Sec[c+d*x]^2,x]*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*
    Int[Simp[(a^2-b^2)*(n+1)-a*b*(n+1)*Csc[c+d*x]+b^2*(n+2)*Csc[c+d*x]^2,x]*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*sec[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


(* ::Subsection::Closed:: *)
(*3 (a+b sec)^m (d sec)^n*)


Int[(a_+b_.*sec[e_.+f_.*x_])*(d_.*sec[e_.+f_.*x_])^n_.,x_Symbol] :=
  a*Int[(d*Sec[e+f*x])^n,x] + b/d*Int[(d*Sec[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,n},x]


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  a*Int[(d*Csc[e+f*x])^n,x] + b/d*Int[(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,n},x]


Int[(a_+b_.*sec[e_.+f_.*x_])^2*(d_.*sec[e_.+f_.*x_])^n_.,x_Symbol] :=
  2*a*b/d*Int[(d*Sec[e+f*x])^(n+1),x] + Int[(d*Sec[e+f*x])^n*(a^2+b^2*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x]


Int[(a_+b_.*csc[e_.+f_.*x_])^2*(d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  2*a*b/d*Int[(d*Csc[e+f*x])^(n+1),x] + Int[(d*Csc[e+f*x])^n*(a^2+b^2*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x]


Int[sec[e_.+f_.*x_]^2/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  1/b*Int[Sec[e+f*x],x] - a/b*Int[Sec[e+f*x]/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f},x]


Int[csc[e_.+f_.*x_]^2/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  1/b*Int[Csc[e+f*x],x] - a/b*Int[Csc[e+f*x]/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x]


Int[sec[e_.+f_.*x_]^3/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  Tan[e+f*x]/(b*f) - a/b*Int[Sec[e+f*x]^2/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f},x]


Int[csc[e_.+f_.*x_]^3/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -Cot[e+f*x]/(b*f) - a/b*Int[Csc[e+f*x]^2/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x]


Int[sec[e_.+f_.*x_]*Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2*b*Tan[e+f*x]/(f*Sqrt[a+b*Sec[e+f*x]]) /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*b*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]) /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Tan[e+f*x]*(a+b*Sec[e+f*x])^(n-1)/(f*n) +
  a*(2*n-1)/n*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(n-1),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Cot[e+f*x]*(a+b*Csc[e+f*x])^(n-1)/(f*n) +
  a*(2*n-1)/n*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[sec[e_.+f_.*x_]/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  Tan[e+f*x]/(f*(b+a*Sec[e+f*x])) /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -Cot[e+f*x]/(f*(b+a*Csc[e+f*x])) /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2/f*Subst[Int[1/(2*a+x^2),x],x,b*Tan[e+f*x]/Sqrt[a+b*Sec[e+f*x]]] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2/f*Subst[Int[1/(2*a+x^2),x],x,b*Cot[e+f*x]/Sqrt[a+b*Csc[e+f*x]]] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Tan[e+f*x]*(a+b*Sec[e+f*x])^n/(a*f*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(n+1),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cot[e+f*x]*(a+b*Csc[e+f*x])^n/(a*f*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*Sqrt[2]*Tan[e+f*x]*(a+b*Sec[e+f*x])^n/(b*f*(2*n+1)*Sqrt[(a-b*Sec[e+f*x])/a])*
    Hypergeometric2F1[1/2,n+1/2,n+3/2,(a+b*Sec[e+f*x])/(2*a)] /;
FreeQ[{a,b,e,f,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*Sqrt[2]*Cot[e+f*x]*(a+b*Csc[e+f*x])^n/(b*f*(2*n+1)*Sqrt[(a-b*Csc[e+f*x])/a])*
    Hypergeometric2F1[1/2,n+1/2,n+3/2,(a+b*Csc[e+f*x])/(2*a)] /;
FreeQ[{a,b,e,f,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_.,x_Symbol] :=
  Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(2*m+1)) + 
  m/(b*(2*m+1))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_.,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(2*m+1)) + 
  m/(b*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_.,x_Symbol] :=
  Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) + 
  a*m/(b*(m+1))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_.,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  a*m/(b*(m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[sec[e_.+f_.*x_]^3*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(a*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(a*m-b*(2*m+1)*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]^3*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  b*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(a*m-b*(2*m+1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[sec[e_.+f_.*x_]^3*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m*(b*(m+1)-a*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[csc[e_.+f_.*x_]^3*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*(b*(m+1)-a*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]*Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2*d/f*Subst[Int[1/Sqrt[1+x^2/a],x],x,b*Tan[e+f*x]/Sqrt[a+b*Sec[e+f*x]]] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && ZeroQ[d-a/b]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*d/f*Subst[Int[1/Sqrt[1+x^2/a],x],x,b*Cot[e+f*x]/Sqrt[a+b*Csc[e+f*x]]] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && ZeroQ[d-a/b]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]*Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2*b*d/f*Subst[Int[1/(b-d*x^2),x],x,b*Tan[e+f*x]/(Sqrt[d*Sec[e+f*x]]*Sqrt[a+b*Sec[e+f*x]])] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && NonzeroQ[d-a/b]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*b*d/f*Subst[Int[1/(b-d*x^2),x],x,b*Cot[e+f*x]/(Sqrt[d*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]])] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && NonzeroQ[d-a/b]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  2*b*d*Tan[e+f*x]*(d*Sec[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Sec[e+f*x]]) + 
  2*a*d*(n-1)/(b*(2*n-1))*Int[Sqrt[a+b*Sec[e+f*x]]*(d*Sec[e+f*x])^(n-1),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*d*Cot[e+f*x]*(d*Csc[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Csc[e+f*x]]) + 
  2*a*d*(n-1)/(b*(2*n-1))*Int[Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1/2 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]/Sqrt[d_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2*a*Tan[e+f*x]/(f*Sqrt[d*Sec[e+f*x]]*Sqrt[a+b*Sec[e+f*x]]) /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*a*Cot[e+f*x]/(f*Sqrt[d*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]) /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*n*Sqrt[a+b*Sec[e+f*x]]) + 
  a*(2*n+1)/(2*b*d*n)*Int[Sqrt[a+b*Sec[e+f*x]]*(d*Sec[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n*Sqrt[a+b*Csc[e+f*x]]) + 
  a*(2*n+1)/(2*b*d*n)*Int[Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1/2 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  2*a*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*Sqrt[a+b*Sec[e+f*x]]*(a*Sec[e+f*x]/b)^n)*
    Hypergeometric2F1[1/2,1-n,3/2,(a-b*Sec[e+f*x])/a] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*Sqrt[a+b*Csc[e+f*x]]*(a*Csc[e+f*x]/b)^n)*
    Hypergeometric2F1[1/2,1-n,3/2,(a-b*Csc[e+f*x])/a] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  a*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n/(f*m) + 
  b*(2*m-1)/(d*m)*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m+n==0 && m>1/2 && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*m) + 
  b*(2*m-1)/(d*m)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m+n==0 && m>1/2 && IntegerQ[2*m]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[2]*Sqrt[a]/(b*f)*Subst[Int[1/Sqrt[1+x^2],x],x,b*Tan[e+f*x]/(a+b*Sec[e+f*x])] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && ZeroQ[d-a/b] && PositiveQ[a]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -Sqrt[2]*Sqrt[a]/(b*f)*Subst[Int[1/Sqrt[1+x^2],x],x,b*Cot[e+f*x]/(a+b*Csc[e+f*x])] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && ZeroQ[d-a/b] && PositiveQ[a]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2*b*d/(a*f)*Subst[Int[1/(2*b-d*x^2),x],x,b*Tan[e+f*x]/(Sqrt[a+b*Sec[e+f*x]]*Sqrt[d*Sec[e+f*x]])] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*b*d/(a*f)*Subst[Int[1/(2*b-d*x^2),x],x,b*Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]])] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)/(a*f*(2*m+1)) + 
  d*(m+1)/(b*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m+n==0 && m<-1/2 && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(a*f*(2*m+1)) + 
  d*(m+1)/(b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m+n==0 && m<-1/2 && IntegerQ[2*m]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  Sqrt[2]*2^m*b*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)/(a*f*((a+b*Sec[e+f*x])/a)^(m+1/2))*((a*Sec[e+f*x])/b)^(m+1/2)*
    Hypergeometric2F1[1/2,1/2-m,3/2,-(a-b*Sec[e+f*x])/(2*b*Sec[e+f*x])] /;
FreeQ[{a,b,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -Sqrt[2]*2^m*b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(a*f*((a+b*Csc[e+f*x])/a)^(m+1/2))*((a*Csc[e+f*x])/b)^(m+1/2)*
    Hypergeometric2F1[1/2,1/2-m,3/2,-(a-b*Csc[e+f*x])/(2*b*Csc[e+f*x])] /;
FreeQ[{a,b,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+n]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*(2*m+1)) + 
  m/(a*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m+n+1==0 && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(2*m+1)) + 
  m/(a*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m+n+1==0 && m<-1/2


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*(m+1)) + 
  a*m/(b*d*(m+1))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+1)) + 
  a*m/(b*d*(m+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^n/(f*n) - 
  a/(d*n)*Int[(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^(n+1)*(b*(m-2*n-2)-a*(m+2*n-1)*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m>1 && (n<-1 || m==3/2 && n==-1/2) && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n/(f*n) - 
  a/(d*n)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^(n+1)*(b*(m-2*n-2)-a*(m+2*n-1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m>1 && (n<-1 || m==3/2 && n==-1/2) && IntegerQ[2*m]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^n/(f*(m+n-1)) + 
  b/(m+n-1)*Int[(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^n*(b*(m+2*n-1)+a*(3*m+2*n-4)*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n/(f*(m+n-1)) + 
  b/(m+n-1)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n*(b*(m+2*n-1)+a*(3*m+2*n-4)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && IntegerQ[2*m]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)/(a*f*(2*m+1)) - 
  d/(a*b*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)*(a*(n-1)-b*(m+n)*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 1<n<2 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(a*f*(2*m+1)) - 
  d/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*(a*(n-1)-b*(m+n)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 1<n<2 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  d^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-2)/(f*(2*m+1)) + 
  d^2/(a*b*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-2)*(b*(n-2)+a*(m-n+2)*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>2 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)/(f*(2*m+1)) + 
  d^2/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)*(b*(n-2)+a*(m-n+2)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>2 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n*(a*(2*m+n+1)-b*(m+n+1)*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*(a*(2*m+n+1)-b*(m+n+1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(d_.*sec[e_.+f_.*x_])^n_/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -d^2*Tan[e+f*x]*(d*Sec[e+f*x])^(n-2)/(f*(a+b*Sec[e+f*x])) - 
  d^2/(a*b)*Int[(d*Sec[e+f*x])^(n-2)*(b*(n-2)-a*(n-1)*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d^2*Cot[e+f*x]*(d*Csc[e+f*x])^(n-2)/(f*(a+b*Csc[e+f*x])) - 
  d^2/(a*b)*Int[(d*Csc[e+f*x])^(n-2)*(b*(n-2)-a*(n-1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[(d_.*sec[e_.+f_.*x_])^n_/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*(a+b*Sec[e+f*x])) - 
  1/a^2*Int[(d*Sec[e+f*x])^n*(a*(n-1)-b*n*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<0


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(a+b*Csc[e+f*x])) - 
  1/a^2*Int[(d*Csc[e+f*x])^n*(a*(n-1)-b*n*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<0


Int[(d_.*sec[e_.+f_.*x_])^n_/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  b*d*Tan[e+f*x]*(d*Sec[e+f*x])^(n-1)/(a*f*(a+b*Sec[e+f*x])) + 
  d*(n-1)/(a*b)*Int[(d*Sec[e+f*x])^(n-1)*(a-b*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*d*Cot[e+f*x]*(d*Csc[e+f*x])^(n-1)/(a*f*(a+b*Csc[e+f*x])) + 
  d*(n-1)/(a*b)*Int[(d*Csc[e+f*x])^(n-1)*(a-b*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && ZeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  d/b*Int[Sqrt[a+b*Sec[e+f*x]]*Sqrt[d*Sec[e+f*x]],x] - 
  a*d/b*Int[Sqrt[d*Sec[e+f*x]]/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  d/b*Int[Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]],x] - 
  a*d/b*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2*d^2*Tan[e+f*x]*(d*Sec[e+f*x])^(n-2)/(f*(2*n-3)*Sqrt[a+b*Sec[e+f*x]]) + 
  d^2/(b*(2*n-3))*Int[(d*Sec[e+f*x])^(n-2)*(2*b*(n-2)-a*Sec[e+f*x])/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[(d_.*csc[e_.+f_.*x_])^n_/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*d^2*Cot[e+f*x]*(d*Csc[e+f*x])^(n-2)/(f*(2*n-3)*Sqrt[a+b*Csc[e+f*x]]) + 
  d^2/(b*(2*n-3))*Int[(d*Csc[e+f*x])^(n-2)*(2*b*(n-2)-a*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[(d_.*sec[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  -Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*n*Sqrt[a+b*Sec[e+f*x]]) + 
  1/(2*b*d*n)*Int[(d*Sec[e+f*x])^(n+1)*(a+b*(2*n+1)*Sec[e+f*x])/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<0 && IntegerQ[2*n]


Int[(d_.*csc[e_.+f_.*x_])^n_/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n*Sqrt[a+b*Csc[e+f*x]]) + 
  1/(2*b*d*n)*Int[(d*Csc[e+f*x])^(n+1)*(a+b*(2*n+1)*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<0 && IntegerQ[2*n]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  d^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-2)/(f*(m+n-1)) + 
  d^2/(b*(m+n-1))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-2)*(b*(n-2)+a*m*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>0 && NonzeroQ[m+n-1] && IntegerQ[n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)/(f*(m+n-1)) + 
  d^2/(b*(m+n-1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)*(b*(n-2)+a*m*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,m},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>0 && NonzeroQ[m+n-1] && IntegerQ[n]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -Sqrt[2]*2^m*d*(a-b*Sec[e+f*x])*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)/
    (b*f*Tan[e+f*x]*((a+b*Sec[e+f*x])/a)^(m-1/2)*((a*Sec[e+f*x])/b)^(n-1))*
    AppellF1[1/2,1/2-m,-n+1,3/2,(a-b*Sec[e+f*x])/(2*a),(a-b*Sec[e+f*x])/a] /;
FreeQ[{a,b,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[m]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Sqrt[2]*2^m*d*(a-b*Csc[e+f*x])*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/
    (b*f*Cot[e+f*x]*((a+b*Csc[e+f*x])/a)^(m-1/2)*((a*Csc[e+f*x])/b)^(n-1))*
    AppellF1[1/2,1/2-m,-n+1,3/2,(a-b*Csc[e+f*x])/(2*a),(a-b*Csc[e+f*x])/a] /;
FreeQ[{a,b,d,e,f,m,n},x] && ZeroQ[a^2-b^2] && Not[IntegerQ[m]]


Int[sec[e_.+f_.*x_]*Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[Cos[e+f*x]]*Sqrt[a+b*Sec[e+f*x]]/Sqrt[b+a*Cos[e+f*x]]*Int[Sqrt[b+a*Cos[e+f*x]]/Cos[e+f*x]^(3/2),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[Sin[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]/Sqrt[b+a*Sin[e+f*x]]*Int[Sqrt[b+a*Sin[e+f*x]]/Sin[e+f*x]^(3/2),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  b*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-1)/(f*m) + 
  1/m*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m-2)*Simp[a^2*m+b^2*(m-1)+a*b*(2*m-1)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)/(f*m) + 
  1/m*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*Simp[a^2*m+b^2*(m-1)+a*b*(2*m-1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


Int[sec[e_.+f_.*x_]/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  1/b*Int[1/(1+a/b*Cos[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  1/b*Int[1/(1+a/b*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


(* Int[sec[e_.+f_.*x_]/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  2*b/f*Subst[Int[1/(b^2*(a+b)-(a-b)*x^2),x],x,b*Tan[e+f*x]/(1+Sec[e+f*x])] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] *)


(* Int[csc[e_.+f_.*x_]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -2*b/f*Subst[Int[1/(b^2*(a+b)-(a-b)*x^2),x],x,b*Cot[e+f*x]/(1+Csc[e+f*x])] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] *)


Int[sec[e_.+f_.*x_]/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b+a*Cos[e+f*x]]/(Sqrt[Cos[e+f*x]]*Sqrt[a+b*Sec[e+f*x]])*Int[1/(Sqrt[Cos[e+f*x]]*Sqrt[b+a*Cos[e+f*x]]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b+a*Sin[e+f*x]]/(Sqrt[Sin[e+f*x]]*Sqrt[a+b*Csc[e+f*x]])*Int[1/(Sqrt[Sin[e+f*x]]*Sqrt[b+a*Sin[e+f*x]]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  b*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*Simp[a*(m+1)-b*(m+2)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*Simp[a*(m+1)-b*(m+2)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
 (a+b*Sec[e+f*x])^(m+1)*Sqrt[b*(1-Sec[e+f*x])/(a+b)]*Sqrt[-b*(1+Sec[e+f*x])/(a-b)]/(b*f*(m+1)*Tan[e+f*x])*
   AppellF1[m+1,1/2,1/2,m+2,(a+b*Sec[e+f*x])/(a-b),(a+b*Sec[e+f*x])/(a+b)] /;
FreeQ[{a,b,e,f,m},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*m]]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
 -(a+b*Csc[e+f*x])^(m+1)*Sqrt[b*(1-Csc[e+f*x])/(a+b)]*Sqrt[-b*(1+Csc[e+f*x])/(a-b)]/(b*f*(m+1)*Cot[e+f*x])*
   AppellF1[m+1,1/2,1/2,m+2,(a+b*Csc[e+f*x])/(a-b),(a+b*Csc[e+f*x])/(a+b)] /;
FreeQ[{a,b,e,f,m},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*m]]


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) + 
  m/(m+1)*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m-1)*(b+a*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  m/(m+1)*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(b+a*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  -a*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) - 
  1/((m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(b*(m+1)-a*(m+2)*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  a*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) - 
  1/((m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(b*(m+1)-a*(m+2)*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[e_.+f_.*x_]^2/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b+a*Cos[e+f*x]]/(Sqrt[Cos[e+f*x]]*Sqrt[a+b*Sec[e+f*x]])*Int[1/(Cos[e+f*x]^(3/2)*Sqrt[b+a*Cos[e+f*x]]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]^2/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b+a*Sin[e+f*x]]/(Sqrt[Sin[e+f*x]]*Sqrt[a+b*Csc[e+f*x]])*Int[1/(Sin[e+f*x]^(3/2)*Sqrt[b+a*Sin[e+f*x]]),x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  -a/b*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m,x] + 1/b*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,m},x] && NonzeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -a/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] + 1/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,m},x] && NonzeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]^3*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  a^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*Simp[a*b*(m+1)-(a^2+b^2*(m+1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^3*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -a^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*Simp[a*b*(m+1)-(a^2+b^2*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[e_.+f_.*x_]^3*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m*(b*(m+1)-a*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[csc[e_.+f_.*x_]^3*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*(b*(m+1)-a*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -a^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Sec[e+f*x])^(m-3)*(d*Sec[e+f*x])^(n+1)*
    Simp[a^2*b*(m-2*n-2)-a*(3*b^2*n+a^2*(n+1))*Sec[e+f*x]-b*(b^2*n+a^2*(m+n-1))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>2 && (IntegerQ[m] && n<-1 || IntegersQ[m+1/2,2*n] && n<=-1)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-3)*(d*Csc[e+f*x])^(n+1)*
    Simp[a^2*b*(m-2*n-2)-a*(3*b^2*n+a^2*(n+1))*Csc[e+f*x]-b*(b^2*n+a^2*(m+n-1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>2 && (IntegerQ[m] && n<-1 || IntegersQ[m+1/2,2*n] && n<=-1)


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^n/(f*(m+n-1)) + 
  1/(d*(m+n-1))*Int[(a+b*Sec[e+f*x])^(m-3)*(d*Sec[e+f*x])^n*
    Simp[a^3*d*(m+n-1)+a*b^2*d*n+b*(b^2*d*(m+n-2)+3*a^2*d*(m+n-1))*Sec[e+f*x]+a*b^2*d*(3*m+2*n-4)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>2 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[IntegerQ[n] && n>2 && Not[IntegerQ[m]]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n/(f*(m+n-1)) + 
  1/(d*(m+n-1))*Int[(a+b*Csc[e+f*x])^(m-3)*(d*Csc[e+f*x])^n*
    Simp[a^3*d*(m+n-1)+a*b^2*d*n+b*(b^2*d*(m+n-2)+3*a^2*d*(m+n-1))*Csc[e+f*x]+a*b^2*d*(3*m+2*n-4)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>2 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[IntegerQ[n] && n>2 && Not[IntegerQ[m]]]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)*
    Simp[b*d*(n-1)+a*d*(m+1)*Sec[e+f*x]-b*d*(m+n+1)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 0<n<1 && IntegersQ[2*m,2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[b*d*(n-1)+a*d*(m+1)*Csc[e+f*x]-b*d*(m+n+1)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 0<n<1 && IntegersQ[2*m,2*n]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*d^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-2)/(f*(m+1)*(a^2-b^2)) - 
  d^2/((m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-2)*(a*(n-2)+b*(m+1)*Sec[e+f*x]-a*(m+n)*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 1<n<2 && IntegersQ[2*m,2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)/(f*(m+1)*(a^2-b^2)) - 
  d^2/((m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)*(a*(n-2)+b*(m+1)*Csc[e+f*x]-a*(m+n)*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 1<n<2 && IntegersQ[2*m,2*n]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*d^3*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-3)/(b*f*(m+1)*(a^2-b^2)) + 
  d^3/(b*(m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-3)*
    Simp[a^2*(n-3)+a*b*(m+1)*Sec[e+f*x]-(a^2*(n-2)+b^2*(m+1))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && (IntegerQ[n] && n>3 || IntegersQ[n+1/2,2*m] && n>2)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -a^2*d^3*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-3)/(b*f*(m+1)*(a^2-b^2)) + 
  d^3/(b*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-3)*
    Simp[a^2*(n-3)+a*b*(m+1)*Csc[e+f*x]-(a^2*(n-2)+b^2*(m+1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && (IntegerQ[n] && n>3 || IntegersQ[n+1/2,2*m] && n>2)


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n/(a*f*n) - 
  1/(a*d*n)*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1)*
    Simp[b*(m+n+1)-a*(n+1)*Sec[e+f*x]-b*(m+n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && NegativeIntegerQ[m+1/2,n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*n) - 
  1/(a*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*
    Simp[b*(m+n+1)-a*(n+1)*Csc[e+f*x]-b*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && NegativeIntegerQ[m+1/2,n]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n*
    (a^2*(m+1)-b^2*(m+n+1)-a*b*(m+1)*Sec[e+f*x]+b^2*(m+n+2)*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegersQ[2*m,2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    (a^2*(m+1)-b^2*(m+n+1)-a*b*(m+1)*Csc[e+f*x]+b^2*(m+n+2)*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegersQ[2*m,2*n]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  Sqrt[d*Cos[e+f*x]]*Sqrt[d*Sec[e+f*x]]/d*Int[Sqrt[d*Cos[e+f*x]]/(b+a*Cos[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  Sqrt[d*Sin[e+f*x]]*Sqrt[d*Csc[e+f*x]]/d*Int[Sqrt[d*Sin[e+f*x]]/(b+a*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^(3/2)/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  d*Sqrt[d*Cos[e+f*x]]*Sqrt[d*Sec[e+f*x]]*Int[1/(Sqrt[d*Cos[e+f*x]]*(b+a*Cos[e+f*x])),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^(3/2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d*Sqrt[d*Sin[e+f*x]]*Sqrt[d*Csc[e+f*x]]*Int[1/(Sqrt[d*Sin[e+f*x]]*(b+a*Sin[e+f*x])),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^(5/2)/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[(d*Sec[e+f*x])^(3/2),x] - a*d/b*Int[(d*Sec[e+f*x])^(3/2)/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^(5/2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[(d*Csc[e+f*x])^(3/2),x] - a*d/b*Int[(d*Csc[e+f*x])^(3/2)/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[d_.*sec[e_.+f_.*x_]]*(a_+b_.*sec[e_.+f_.*x_])),x_Symbol] :=
  b^2/(a^2*d^2)*Int[(d*Sec[e+f*x])^(3/2)/(a+b*Sec[e+f*x]),x] + 
  1/a^2*Int[(a-b*Sec[e+f*x])/Sqrt[d*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[d_.*csc[e_.+f_.*x_]]*(a_+b_.*csc[e_.+f_.*x_])),x_Symbol] :=
  b^2/(a^2*d^2)*Int[(d*Csc[e+f*x])^(3/2)/(a+b*Csc[e+f*x]),x] + 
  1/a^2*Int[(a-b*Csc[e+f*x])/Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^n_/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -Tan[e+f*x]*(d*Sec[e+f*x])^n/(a*f*n) - 
  1/(a*d*n)*Int[(d*Sec[e+f*x])^(n+1)/(a+b*Sec[e+f*x])*
    Simp[b*n-a*(n+1)*Sec[e+f*x]-b*(n+1)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  Cot[e+f*x]*(d*Csc[e+f*x])^n/(a*f*n) - 
  1/(a*d*n)*Int[(d*Csc[e+f*x])^(n+1)/(a+b*Csc[e+f*x])*
    Simp[b*n-a*(n+1)*Csc[e+f*x]-b*(n+1)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]*Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  a*Int[Sqrt[d*Sec[e+f*x]]/Sqrt[a+b*Sec[e+f*x]],x] + 
  b/d*Int[(d*Sec[e+f*x])^(3/2)/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  a*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] + 
  b/d*Int[(d*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^n_*Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2*d*Sin[e+f*x]*(d*Sec[e+f*x])^(n-1)*Sqrt[a+b*Sec[e+f*x]]/(f*(2*n-1)) + 
  d^2/(2*n-1)*Int[(d*Sec[e+f*x])^(n-2)*Simp[2*a*(n-2)+b*(2*n-3)*Sec[e+f*x]+a*Sec[e+f*x]^2,x]/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[(d_.*csc[e_.+f_.*x_])^n_*Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*d*Cos[e+f*x]*(d*Csc[e+f*x])^(n-1)*Sqrt[a+b*Csc[e+f*x]]/(f*(2*n-1)) + 
  d^2/(2*n-1)*Int[(d*Csc[e+f*x])^(n-2)*Simp[2*a*(n-2)+b*(2*n-3)*Csc[e+f*x]+a*Csc[e+f*x]^2,x]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]/Sqrt[d_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[a+b*Sec[e+f*x]]/(Sqrt[d*Sec[e+f*x]]*Sqrt[b+a*Cos[e+f*x]])*Int[Sqrt[b+a*Cos[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[a+b*Csc[e+f*x]]/(Sqrt[d*Csc[e+f*x]]*Sqrt[b+a*Sin[e+f*x]])*Int[Sqrt[b+a*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -Tan[e+f*x]*(d*Sec[e+f*x])^n*Sqrt[a+b*Sec[e+f*x]]/(f*n) - 
  1/(2*d*n)*Int[(d*Sec[e+f*x])^(n+1)*Simp[b-2*a*(n+1)*Sec[e+f*x]-b*(2*n+3)*Sec[e+f*x]^2,x]/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Cot[e+f*x]*(d*Csc[e+f*x])^n*Sqrt[a+b*Csc[e+f*x]]/(f*n) - 
  1/(2*d*n)*Int[(d*Csc[e+f*x])^(n+1)*Simp[b-2*a*(n+1)*Csc[e+f*x]-b*(2*n+3)*Csc[e+f*x]^2,x]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[d*Sec[e+f*x]]*Sqrt[b+a*Cos[e+f*x]]/Sqrt[a+b*Sec[e+f*x]]*Int[1/Sqrt[b+a*Cos[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[d*Csc[e+f*x]]*Sqrt[b+a*Sin[e+f*x]]/Sqrt[a+b*Csc[e+f*x]]*Int[1/Sqrt[b+a*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  d*Sqrt[d*Sec[e+f*x]]*Sqrt[b+a*Cos[e+f*x]]/Sqrt[a+b*Sec[e+f*x]]*Int[Sec[e+f*x]/Sqrt[b+a*Cos[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  d*Sqrt[d*Csc[e+f*x]]*Sqrt[b+a*Sin[e+f*x]]/Sqrt[a+b*Csc[e+f*x]]*Int[Csc[e+f*x]/Sqrt[b+a*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  2*d^2*Sin[e+f*x]*(d*Sec[e+f*x])^(n-2)*Sqrt[a+b*Sec[e+f*x]]/(b*f*(2*n-3)) + 
  d^3/(b*(2*n-3))*Int[(d*Sec[e+f*x])^(n-3)/Sqrt[a+b*Sec[e+f*x]]*
    Simp[2*a*(n-3)+b*(2*n-5)*Sec[e+f*x]-2*a*(n-2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[(d_.*csc[e_.+f_.*x_])^n_/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*d^2*Cos[e+f*x]*(d*Csc[e+f*x])^(n-2)*Sqrt[a+b*Csc[e+f*x]]/(b*f*(2*n-3)) + 
  d^3/(b*(2*n-3))*Int[(d*Csc[e+f*x])^(n-3)/Sqrt[a+b*Csc[e+f*x]]*
     Simp[2*a*(n-3)+b*(2*n-5)*Csc[e+f*x]-2*a*(n-2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[1/(sec[e_.+f_.*x_]*Sqrt[a_+b_.*sec[e_.+f_.*x_]]),x_Symbol] :=
  Sin[e+f*x]*Sqrt[a+b*Sec[e+f*x]]/(a*f) - b/(2*a)*Int[(1+Sec[e+f*x]^2)/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[1/(csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  -Cos[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/(a*f) - b/(2*a)*Int[(1+Csc[e+f*x]^2)/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[d_.*sec[e_.+f_.*x_]]*Sqrt[a_+b_.*sec[e_.+f_.*x_]]),x_Symbol] :=
  1/a*Int[Sqrt[a+b*Sec[e+f*x]]/Sqrt[d*Sec[e+f*x]],x] - 
  b/(a*d)*Int[Sqrt[d*Sec[e+f*x]]/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[1/(Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  1/a*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[d*Csc[e+f*x]],x] - 
  b/(a*d)*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  -Sin[e+f*x]*(d*Sec[e+f*x])^(n+1)*Sqrt[a+b*Sec[e+f*x]]/(a*d*f*n) + 
  1/(2*a*d*n)*Int[(d*Sec[e+f*x])^(n+1)/Sqrt[a+b*Sec[e+f*x]]*
    Simp[-b*(2*n+1)+2*a*(n+1)*Sec[e+f*x]+b*(2*n+3)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(d_.*csc[e_.+f_.*x_])^n_/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Cos[e+f*x]*(d*Csc[e+f*x])^(n+1)*Sqrt[a+b*Csc[e+f*x]]/(a*d*f*n) + 
  1/(2*a*d*n)*Int[(d*Csc[e+f*x])^(n+1)/Sqrt[a+b*Csc[e+f*x]]*
    Simp[-b*(2*n+1)+2*a*(n+1)*Csc[e+f*x]+b*(2*n+3)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*sec[e_.+f_.*x_])^(3/2)*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*Tan[e+f*x]*Sqrt[a+b*Sec[e+f*x]]*(d*Sec[e+f*x])^n/(f*n) + 
  1/(2*d*n)*Int[(d*Sec[e+f*x])^(n+1)/Sqrt[a+b*Sec[e+f*x]]*
    Simp[a*b*(2*n-1)+2*(b^2*n+a^2*(n+1))*Sec[e+f*x]+a*b*(2*n+3)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegersQ[2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*Cot[e+f*x]*Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^n/(f*n) + 
  1/(2*d*n)*Int[(d*Csc[e+f*x])^(n+1)/Sqrt[a+b*Csc[e+f*x]]*
    Simp[a*b*(2*n-1)+2*(b^2*n+a^2*(n+1))*Csc[e+f*x]+a*b*(2*n+3)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegersQ[2*n]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  d^3*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-3)/(b*f*(m+n-1)) + 
  d^3/(b*(m+n-1))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-3)*
    Simp[a*(n-3)+b*(m+n-2)*Sec[e+f*x]-a*(n-2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>3 && 
  (IntegerQ[n] || IntegersQ[2*m,2*n]) && Not[IntegerQ[m] && m>2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d^3*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-3)/(b*f*(m+n-1)) + 
  d^3/(b*(m+n-1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-3)*
    Simp[a*(n-3)+b*(m+n-2)*Csc[e+f*x]-a*(n-2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>3 && 
  (IntegerQ[n] || IntegersQ[2*m,2*n]) && Not[IntegerQ[m] && m>2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n-1)/(f*(m+n-1)) + 
  d/(m+n-1)*Int[(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^(n-1)*
    Simp[a*b*(n-1)+(b^2*(m+n-2)+a^2*(m+n-1))*Sec[e+f*x]+a*b*(2*m+n-2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 0<m<2 && 0<n<3 && NonzeroQ[m+n-1] && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n-1)/(f*(m+n-1)) + 
  d/(m+n-1)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^(n-1)*
    Simp[a*b*(n-1)+(b^2*(m+n-2)+a^2*(m+n-1))*Csc[e+f*x]+a*b*(2*m+n-2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 0<m<2 && 0<n<3 && NonzeroQ[m+n-1] && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  d^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-2)/(f*(m+n-1)) + 
  d^2/(b*(m+n-1))*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n-2)*
    Simp[a*b*(n-2)+b^2*(m+n-2)*Sec[e+f*x]+a*b*m*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 1<n<3 && -1<m<2 && NonzeroQ[m+n-1] && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)/(f*(m+n-1)) + 
  d^2/(b*(m+n-1))*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n-2)*
    Simp[a*b*(n-2)+b^2*(m+n-2)*Csc[e+f*x]+a*b*m*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 1<n<3 && -1<m<2 && NonzeroQ[m+n-1] && (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(a_+b_.*sec[e_.+f_.*x_])^(3/2)/Sqrt[d_.*sec[e_.+f_.*x_]],x_Symbol] :=
  a*Int[Sqrt[a+b*Sec[e+f*x]]/Sqrt[d*Sec[e+f*x]],x] + 
  b/d*Int[Sqrt[d*Sec[e+f*x]]*Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)/Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  a*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[d*Csc[e+f*x]],x] + 
  b/d*Int[Sqrt[d*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b/d*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n+1),x] + 
  a*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,n},x] && PositiveIntegerQ[m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b/d*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1),x] + 
  a*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,n},x] && PositiveIntegerQ[m]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,m,n},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,m,n},x] && NonzeroQ[a^2-b^2]


(* ::Subsection::Closed:: *)
(*4 (a+b sec)^m (d sec)^n (A+B sec)*)


Int[(a_+b_.*sec[e_.+f_.*x_])*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -A*a*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Sec[e+f*x])^(n+1)*Simp[n*(B*a+A*b)+(B*b*n+A*a*(n+1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Csc[e+f*x])^(n+1)*Simp[n*(B*a+A*b)+(B*b*n+A*a*(n+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && RationalQ[n] && n<=-1


Int[(a_+b_.*sec[e_.+f_.*x_])*(d_.*sec[e_.+f_.*x_])^n_.*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  b*B*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*(n+1)) + 
  1/(n+1)*Int[(d*Sec[e+f*x])^n*Simp[A*a*(n+1)+B*b*n+(A*b+B*a)*(n+1)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[n] && n<=-1]


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_.*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(n+1)) + 
  1/(n+1)*Int[(d*Csc[e+f*x])^n*Simp[A*a*(n+1)+B*b*n+(A*b+B*a)*(n+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[n] && n<=-1]


Int[sec[e_.+f_.*x_]*(A_+B_.*sec[e_.+f_.*x_])/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  B/b*Int[Sec[e+f*x],x] + (A*b-a*B)/b*Int[Sec[e+f*x]/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B]


Int[csc[e_.+f_.*x_]*(A_+B_.*csc[e_.+f_.*x_])/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  B/b*Int[Csc[e+f*x],x] + (A*b-a*B)/b*Int[Csc[e+f*x]/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_.*(c_+d_.*sec[e_.+f_.*x_]),x_Symbol] :=
  d*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[a*d*m+b*c*(m+1)]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && ZeroQ[a*d*m+b*c*(m+1)]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_.*(c_+d_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(a*f*(2*m+1)) + 
  (a*d*m+b*c*(m+1))/(a*b*(2*m+1))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[a*d*m+b*c*(m+1)] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) + 
  (a*d*m+b*c*(m+1))/(a*b*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[a*d*m+b*c*(m+1)] && RationalQ[m] && m<-1/2


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_.*(c_+d_.*sec[e_.+f_.*x_]),x_Symbol] :=
  d*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) + 
  (a*d*m+b*c*(m+1))/(b*(m+1))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[a*d*m+b*c*(m+1)] && Not[RationalQ[m] && m<-1/2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  (a*d*m+b*c*(m+1))/(b*(m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[a^2-b^2] && NonzeroQ[a*d*m+b*c*(m+1)] && Not[RationalQ[m] && m<-1/2]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(c_+d_.*sec[e_.+f_.*x_]),x_Symbol] :=
  d*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m-1)*Simp[b*d*m+a*c*(m+1)+(a*d*m+b*c*(m+1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*Simp[b*d*m+a*c*(m+1)+(a*d*m+b*c*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(c_+d_.*sec[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*Simp[(a*c-b*d)*(m+1)-(c*b-a*d)*(m+2)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*Simp[(a*c-b*d)*(m+1)-(c*b-a*d)*(m+2)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[e_.+f_.*x_]*(c_+d_.*sec[e_.+f_.*x_])/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b+a*Cos[e+f*x]]/(Sqrt[Cos[e+f*x]]*Sqrt[a+b*Sec[e+f*x]])*
    Int[(d+c*Cos[e+f*x])/(Cos[e+f*x]^(3/2)*Sqrt[b+a*Cos[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(c_+d_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b+a*Sin[e+f*x]]/(Sqrt[Sin[e+f*x]]*Sqrt[a+b*Csc[e+f*x]])*
    Int[(d+c*Sin[e+f*x])/(Sin[e+f*x]^(3/2)*Sqrt[b+a*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(c_+d_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -2*Sqrt[2]*c*(a+b*Sec[e+f*x])^m*(c-d*Sec[e+f*x])*Sqrt[(c+d*Sec[e+f*x])/c]/(d*f*Tan[e+f*x]*((c*(a+b*Sec[e+f*x]))/(a*c+b*d))^m)*
    AppellF1[1/2,-(1/2),-m,3/2,(c-d*Sec[e+f*x])/(2*c),(b*(c-d*Sec[e+f*x]))/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[IntegerQ[2*m]]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  2*Sqrt[2]*c*(a+b*Csc[e+f*x])^m*(c-d*Csc[e+f*x])*Sqrt[(c+d*Csc[e+f*x])/c]/(d*f*Cot[e+f*x]*((c*(a+b*Csc[e+f*x]))/(a*c+b*d))^m)*
    AppellF1[1/2,-(1/2),-m,3/2,(c-d*Csc[e+f*x])/(2*c),(b*(c-d*Csc[e+f*x]))/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && ZeroQ[c^2-d^2] && Not[IntegerQ[2*m]]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(c_+d_.*sec[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)/b*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m,x] + d/b*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] + d/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2]


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(b*f*(2*m+1)) + 
  1/(b^2*(2*m+1))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*Simp[A*b*m-a*B*m+b*B*(2*m+1)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(b*f*(2*m+1)) + 
  1/(b^2*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*Simp[A*b*m-a*B*m+b*B*(2*m+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -a*(A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) - 
  1/(b*(m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*
    Simp[b*(A*b-a*B)*(m+1)-(a*A*b*(m+2)-B*(a^2+b^2*(m+1)))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) - 
  1/(b*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[b*(A*b-a*B)*(m+1)-(a*A*b*(m+2)-B*(a^2+b^2*(m+1)))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_.*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  B*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m*Simp[b*B*(m+1)+(A*b*(m+2)-a*B)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[m] && m<-1]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*Simp[b*B*(m+1)+(A*b*(m+2)-a*B)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*n) /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && ZeroQ[a*A*m-b*B*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && ZeroQ[a*A*m-b*B*n]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(b*f*(2*m+1)) + 
  (a*A*m+b*B*(m+1))/(a^2*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && RationalQ[m] && m<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(b*f*(2*m+1)) + 
  (a*A*m+b*B*(m+1))/(a^2*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && RationalQ[m] && m<=-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*n) - 
  (a*A*m-b*B*n)/(b*d*n)*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && Not[RationalQ[m] && m<=-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  (a*A*m-b*B*n)/(b*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[m+n+1] && Not[RationalQ[m] && m<=-1]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  2*b*B*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Sec[e+f*x]]) /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[A*b*(2*n+1)+2*a*B*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -2*b*B*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Csc[e+f*x]]) /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && ZeroQ[A*b*(2*n+1)+2*a*B*n]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -A*b^2*Tan[e+f*x]*(d*Sec[e+f*x])^n/(a*f*n*Sqrt[a+b*Sec[e+f*x]]) + 
  (A*b*(2*n+1)+2*a*B*n)/(2*a*d*n)*Int[Sqrt[a+b*Sec[e+f*x]]*(d*Sec[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[A*b*(2*n+1)+2*a*B*n] && RationalQ[n] && n<0


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*b^2*Cot[e+f*x]*(d*Csc[e+f*x])^n/(a*f*n*Sqrt[a+b*Csc[e+f*x]]) + 
  (A*b*(2*n+1)+2*a*B*n)/(2*a*d*n)*Int[Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[A*b*(2*n+1)+2*a*B*n] && RationalQ[n] && n<0


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  2*b*B*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Sec[e+f*x]]) + 
  (A*b*(2*n+1)+2*a*B*n)/(b*(2*n+1))*Int[Sqrt[a+b*Sec[e+f*x]]*(d*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[A*b*(2*n+1)+2*a*B*n] && Not[RationalQ[n] && n<0]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -2*b*B*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Csc[e+f*x]]) + 
  (A*b*(2*n+1)+2*a*B*n)/(b*(2*n+1))*Int[Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && NonzeroQ[A*b*(2*n+1)+2*a*B*n] && Not[RationalQ[n] && n<0]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -a*A*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n/(f*n) - 
  b/(a*d*n)*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n+1)*Simp[a*A*(m-n-1)-b*B*n-(a*B*n+A*b*(m+n))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m>1/2 && n<-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*n) - 
  b/(a*d*n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1)*Simp[a*A*(m-n-1)-b*B*n-(a*B*n+A*b*(m+n))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m>1/2 && n<-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  b*B*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n/(f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n*Simp[a*A*d*(m+n)+B*(b*d*n)+(A*b*d*(m+n)+a*B*d*(2*m+n-1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2 && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n*Simp[a*A*d*(m+n)+B*(b*d*n)+(A*b*d*(m+n)+a*B*d*(2*m+n-1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2 && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -d*(A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)*
    Simp[A*(a*d*(n-1))-B*(b*d*(n-1))-d*(a*B*(m-n+1)+A*b*(m+n))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m<-1/2 && n>0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[A*(a*d*(n-1))-B*(b*d*(n-1))-d*(a*B*(m-n+1)+A*b*(m+n))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m,n] && m<-1/2 && n>0


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(b*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n*
    Simp[b*B*n-a*A*(2*m+n+1)+(A*b-a*B)*(m+n+1)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2 && Not[RationalQ[n] && n>0]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(b*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[b*B*n-a*A*(2*m+n+1)+(A*b-a*B)*(m+n+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2 && Not[RationalQ[n] && n>0]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]*(A_+B_.*sec[e_.+f_.*x_])/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  B/b*Int[Sqrt[a+b*Sec[e+f*x]]*Sqrt[d*Sec[e+f*x]],x] + 
  (A*b-a*B)/b*Int[Sqrt[d*Sec[e+f*x]]/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]*(A_+B_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  B/b*Int[Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]],x] + 
  (A*b-a*B)/b*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  B*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)/(f*(m+n)) + 
  d/(b*(m+n))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)*Simp[b*B*(n-1)+(A*b*(m+n)+a*B*m)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(f*(m+n)) + 
  d/(b*(m+n))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)*Simp[b*B*(n-1)+(A*b*(m+n)+a*B*m)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1)*Simp[a*A*m-b*B*n-A*b*(m+n+1)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n<0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*Simp[a*A*m-b*B*n-A*b*(m+n+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[n] && n<0


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n,x] + 
  B/b*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n,x] + 
  B/b*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -a*A*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^(n+1)*
    Simp[a*(a*B*n-A*b*(m-n-1))+(2*a*b*B*n+A*(b^2*n+a^2*(1+n)))*Sec[e+f*x]+b*(b*B*n+a*A*(m+n))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>1 && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^(n+1)*
    Simp[a*(a*B*n-A*b*(m-n-1))+(2*a*b*B*n+A*(b^2*n+a^2*(1+n)))*Csc[e+f*x]+b*(b*B*n+a*A*(m+n))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>1 && n<=-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  b*B*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n/(f*(m+n)) + 
  1/(m+n)*Int[(a+b*Sec[e+f*x])^(m-2)*(d*Sec[e+f*x])^n*
    Simp[a^2*A*(m+n)+a*b*B*n+(a*(2*A*b+a*B)*(m+n)+b^2*B*(m+n-1))*Sec[e+f*x]+b*(A*b*(m+n)+a*B*(2*m+n-1))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && Not[IntegerQ[n] && n>1 && 
  Not[IntegerQ[m]]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*(m+n)) + 
  1/(m+n)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n*
    Simp[a^2*A*(m+n)+a*b*B*n+(a*(2*A*b+a*B)*(m+n)+b^2*B*(m+n-1))*Csc[e+f*x]+b*(A*b*(m+n)+a*B*(2*m+n-1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1 && Not[IntegerQ[n] && n>1 && 
  Not[IntegerQ[m]]]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  d*(A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)*
    Simp[d*(n-1)*(A*b-a*B)+d*(a*A-b*B)*(m+1)*Sec[e+f*x]-d*(A*b-a*B)*(m+n+1)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 0<n<1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -d*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[d*(n-1)*(A*b-a*B)+d*(a*A-b*B)*(m+1)*Csc[e+f*x]-d*(A*b-a*B)*(m+n+1)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 0<n<1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -a*d^2*(A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-2)/(b*f*(m+1)*(a^2-b^2)) - 
  d/(b*(m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-2)*
    Simp[a*d*(A*b-a*B)*(n-2)+b*d*(A*b-a*B)*(m+1)*Sec[e+f*x]-(a*A*b*d*(m+n)-d*B*(a^2*(n-1)+b^2*(m+1)))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*d^2*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)/(b*f*(m+1)*(a^2-b^2)) - 
  d/(b*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)*
    Simp[a*d*(A*b-a*B)*(n-2)+b*d*(A*b-a*B)*(m+1)*Csc[e+f*x]-(a*A*b*d*(m+n)-d*B*(a^2*(n-1)+b^2*(m+1)))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -b*(A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n*
    Simp[A*(a^2*(m+1)-b^2*(m+n+1))+a*b*B*n-a*(A*b-a*B)*(m+1)*Sec[e+f*x]+b*(A*b-a*B)*(m+n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  b*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[A*(a^2*(m+1)-b^2*(m+n+1))+a*b*B*n-a*(A*b-a*B)*(m+1)*Csc[e+f*x]+b*(A*b-a*B)*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  B*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)/(f*(m+n)) + 
  d/(m+n)*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n-1)*
    Simp[a*B*(n-1)+(b*B*(m+n-1)+a*A*(m+n))*Sec[e+f*x]+(a*B*m+A*b*(m+n))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 0<m<1 && n>0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(f*(m+n)) + 
  d/(m+n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n-1)*
    Simp[a*B*(n-1)+(b*B*(m+n-1)+a*A*(m+n))*Csc[e+f*x]+(a*B*m+A*b*(m+n))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 0<m<1 && n>0


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n+1)*
    Simp[A*b*m-a*B*n-(b*B*n+a*A*(n+1))*Sec[e+f*x]-A*b*(m+n+1)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 0<m<1 && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1)*
    Simp[A*b*m-a*B*n-(b*B*n+a*A*(n+1))*Csc[e+f*x]-A*b*(m+n+1)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 0<m<1 && n<=-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  B*d^2*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-2)/(b*f*(m+n)) + 
  d^2/(b*(m+n))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-2)*
    Simp[a*B*(n-2)+B*b*(m+n-1)*Sec[e+f*x]+(A*b*(m+n)-a*B*(n-1))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && NonzeroQ[m+n] && 
  Not[IntegerQ[m] && m>1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)/(b*f*(m+n)) + 
  d^2/(b*(m+n))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)*
    Simp[a*B*(n-2)+B*b*(m+n-1)*Csc[e+f*x]+(A*b*(m+n)-a*B*(n-1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && NonzeroQ[m+n] && 
  Not[IntegerQ[m] && m>1]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1)*
    Simp[a*B*n-A*b*(m+n+1)+A*a*(n+1)*Sec[e+f*x]+A*b*(m+n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*
    Simp[a*B*n-A*b*(m+n+1)+A*a*(n+1)*Csc[e+f*x]+A*b*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(A_+B_.*sec[e_.+f_.*x_])/(Sqrt[d_.*sec[e_.+f_.*x_]]*Sqrt[a_+b_.*sec[e_.+f_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Sec[e+f*x]]/Sqrt[d*Sec[e+f*x]],x] - 
  (A*b-a*B)/(a*d)*Int[Sqrt[d*Sec[e+f*x]]/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[e_.+f_.*x_])/(Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[d*Csc[e+f*x]],x] - 
  (A*b-a*B)/(a*d)*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[d_.*sec[e_.+f_.*x_]]*(A_+B_.*sec[e_.+f_.*x_])/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  A*Int[Sqrt[d*Sec[e+f*x]]/Sqrt[a+b*Sec[e+f*x]],x] + 
  B/d*Int[(d*Sec[e+f*x])^(3/2)/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]*(A_+B_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  A*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] + 
  B/d*Int[(d*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(A_+B_.*sec[e_.+f_.*x_])/Sqrt[d_.*sec[e_.+f_.*x_]],x_Symbol] :=
  B/d*Int[Sqrt[a+b*Sec[e+f*x]]*Sqrt[d*Sec[e+f*x]],x] + 
  A*Int[Sqrt[a+b*Sec[e+f*x]]/Sqrt[d*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(A_+B_.*csc[e_.+f_.*x_])/Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  B/d*Int[Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]],x] + 
  A*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(d_.*sec[e_.+f_.*x_])^n_*(A_+B_.*sec[e_.+f_.*x_])/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  A/a*Int[(d*Sec[e+f*x])^n,x] - (A*b-a*B)/(a*d)*Int[(d*Sec[e+f*x])^(n+1)/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_])/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A/a*Int[(d*Csc[e+f*x])^n,x] - (A*b-a*B)/(a*d)*Int[(d*Csc[e+f*x])^(n+1)/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_.*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  Defer[Int][(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n*(A+B*Sec[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*(A+B*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


(* ::Subsection::Closed:: *)
(*5 (a+b sec)^m (A+B sec+C sec^2)*)


Int[(a_+b_.*sec[c_.+d_.*x_])^m_.*(A_.+B_.*sec[c_.+d_.*x_]+C_.*sec[c_.+d_.*x_]^2),x_Symbol] :=
  1/b^2*Int[(a+b*Sec[c+d*x])^(m+1)*Simp[b*B-a*C+b*C*Sec[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(a_+b_.*csc[c_.+d_.*x_])^m_.*(A_.+B_.*csc[c_.+d_.*x_]+C_.*csc[c_.+d_.*x_]^2),x_Symbol] :=
  1/b^2*Int[(a+b*Csc[c+d*x])^(m+1)*Simp[b*B-a*C+b*C*Csc[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,B,C,m},x] && ZeroQ[A*b^2-a*b*B+a^2*C]


Int[(a_+b_.*sec[c_.+d_.*x_])^m_.*(A_.+C_.*sec[c_.+d_.*x_]^2),x_Symbol] :=
  C/b^2*Int[(a+b*Sec[c+d*x])^(m+1)*Simp[-a+b*Sec[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[A*b^2+a^2*C]


Int[(a_+b_.*csc[c_.+d_.*x_])^m_.*(A_.+C_.*csc[c_.+d_.*x_]^2),x_Symbol] :=
  C/b^2*Int[(a+b*Csc[c+d*x])^(m+1)*Simp[-a+b*Csc[c+d*x],x],x] /;
FreeQ[{a,b,c,d,A,C,m},x] && ZeroQ[A*b^2+a^2*C]


Int[(b_.*sec[e_.+f_.*x_])^m_.*(A_+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*Tan[e+f*x]*(b*Sec[e+f*x])^m/(f*m) /;
FreeQ[{b,e,f,A,C,m},x] && ZeroQ[C*m+A*(m+1)]


Int[(b_.*csc[e_.+f_.*x_])^m_.*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(b*Csc[e+f*x])^m/(f*m) /;
FreeQ[{b,e,f,A,C,m},x] && ZeroQ[C*m+A*(m+1)]


Int[(b_.*sec[e_.+f_.*x_])^m_.*(A_+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*Tan[e+f*x]*(b*Sec[e+f*x])^m/(f*m) + 
  (C*m+A*(m+1))/(b^2*m)*Int[(b*Sec[e+f*x])^(m+2),x] /;
FreeQ[{b,e,f,A,C},x] && NonzeroQ[C*m+A*(m+1)] && RationalQ[m] && m<=-1


Int[(b_.*csc[e_.+f_.*x_])^m_.*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(b*Csc[e+f*x])^m/(f*m) + 
  (C*m+A*(m+1))/(b^2*m)*Int[(b*Csc[e+f*x])^(m+2),x] /;
FreeQ[{b,e,f,A,C},x] && NonzeroQ[C*m+A*(m+1)] && RationalQ[m] && m<=-1


Int[(b_.*sec[e_.+f_.*x_])^m_.*(A_+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(b*Sec[e+f*x])^m/(f*(m+1)) + 
  (C*m+A*(m+1))/(m+1)*Int[(b*Sec[e+f*x])^m,x] /;
FreeQ[{b,e,f,A,C,m},x] && NonzeroQ[C*m+A*(m+1)] && Not[RationalQ[m] && m<=-1]


Int[(b_.*csc[e_.+f_.*x_])^m_.*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(b*Csc[e+f*x])^m/(f*(m+1)) + 
  (C*m+A*(m+1))/(m+1)*Int[(b*Csc[e+f*x])^m,x] /;
FreeQ[{b,e,f,A,C,m},x] && NonzeroQ[C*m+A*(m+1)] && Not[RationalQ[m] && m<=-1]


Int[(b_.*sec[e_.+f_.*x_])^m_.*(B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  B/b*Int[(b*Sec[e+f*x])^(m+1),x] + C/b^2*Int[(b*Sec[e+f*x])^(m+2),x] /;
FreeQ[{b,e,f,B,C,m},x]


Int[(b_.*csc[e_.+f_.*x_])^m_.*(B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  B/b*Int[(b*Csc[e+f*x])^(m+1),x] + C/b^2*Int[(b*Csc[e+f*x])^(m+2),x] /;
FreeQ[{b,e,f,B,C,m},x]


Int[(b_.*sec[e_.+f_.*x_])^m_.*(A_+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  B/b*Int[(b*Sec[e+f*x])^(m+1),x] + Int[(A+C*Sec[e+f*x]^2)*(b*Sec[e+f*x])^m,x] /;
FreeQ[{b,e,f,A,B,C,m},x]


Int[(b_.*csc[e_.+f_.*x_])^m_.*(A_+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  B/b*Int[(b*Csc[e+f*x])^(m+1),x] + Int[(A+C*Csc[e+f*x]^2)*(b*Csc[e+f*x])^m,x] /;
FreeQ[{b,e,f,A,B,C,m},x]


Int[(a_+b_.*sec[e_.+f_.*x_])*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  b*C*Sec[e+f*x]*Tan[e+f*x]/(2*f) + 
  1/2*Int[Simp[2*A*a+(2*B*a+b*(2*A+C))*Sec[e+f*x]+2*(a*C+B*b)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x]


Int[(a_+b_.*csc[e_.+f_.*x_])*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Csc[e+f*x]*Cot[e+f*x]/(2*f) + 
  1/2*Int[Simp[2*A*a+(2*B*a+b*(2*A+C))*Csc[e+f*x]+2*(a*C+B*b)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x]


Int[(a_+b_.*sec[e_.+f_.*x_])*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  b*C*Sec[e+f*x]*Tan[e+f*x]/(2*f) + 
  1/2*Int[Simp[2*A*a+b*(2*A+C)*Sec[e+f*x]+2*a*C*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x]


Int[(a_+b_.*csc[e_.+f_.*x_])*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Csc[e+f*x]*Cot[e+f*x]/(2*f) + 
  1/2*Int[Simp[2*A*a+b*(2*A+C)*Csc[e+f*x]+2*a*C*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x]


Int[(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2)/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  C/b*Int[Sec[e+f*x],x] + 1/b*Int[(A*b+(b*B-a*C)*Sec[e+f*x])/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B,C},x]


Int[(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  C/b*Int[Csc[e+f*x],x] + 1/b*Int[(A*b+(b*B-a*C)*Csc[e+f*x])/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B,C},x]


Int[(A_.+C_.*sec[e_.+f_.*x_]^2)/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  C/b*Int[Sec[e+f*x],x] + 1/b*Int[(A*b-a*C*Sec[e+f*x])/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,C},x]


Int[(A_.+C_.*csc[e_.+f_.*x_]^2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  C/b*Int[Csc[e+f*x],x] + 1/b*Int[(A*b-a*C*Csc[e+f*x])/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,C},x]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A-b*B+a*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*Simp[A*b*(2*m+1)+(b*B*(m+1)-a*(A*(m+1)-C*m))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A-b*B+a*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*Simp[A*b*(2*m+1)+(b*B*(m+1)-a*(A*(m+1)-C*m))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A+C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*Simp[A*b*(2*m+1)-a*(A*(m+1)-C*m)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A+C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*Simp[A*b*(2*m+1)-a*(A*(m+1)-C*m)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) + 
  1/(b*(m+1))*Int[(a+b*Sec[e+f*x])^m*Simp[A*b*(m+1)+(a*C*m+b*B*(m+1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(b*(m+1))*Int[(a+b*Csc[e+f*x])^m*Simp[A*b*(m+1)+(a*C*m+b*B*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) + 
  1/(b*(m+1))*Int[(a+b*Sec[e+f*x])^m*Simp[A*b*(m+1)+a*C*m*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(b*(m+1))*Int[(a+b*Csc[e+f*x])^m*Simp[A*b*(m+1)+a*C*m*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Sec[e+f*x])^(m-1)*
    Simp[a*A*(m+1)+((A*b+a*B)*(m+1)+b*C*m)*Sec[e+f*x]+(b*B*(m+1)+a*C*m)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Csc[e+f*x])^(m-1)*
    Simp[a*A*(m+1)+((A*b+a*B)*(m+1)+b*C*m)*Csc[e+f*x]+(b*B*(m+1)+a*C*m)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[2*m]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Sec[e+f*x])^(m-1)*Simp[a*A*(m+1)+(A*b*(m+1)+b*C*m)*Sec[e+f*x]+a*C*m*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Csc[e+f*x])^(m-1)*Simp[a*A*(m+1)+(A*b*(m+1)+b*C*m)*Csc[e+f*x]+a*C*m*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2] && PositiveIntegerQ[2*m]


Int[(A_+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2)/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Int[(A+(B-C)*Sec[e+f*x])/Sqrt[a+b*Sec[e+f*x]],x] + C*Int[Sec[e+f*x]*(1+Sec[e+f*x])/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Int[(A+(B-C)*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] + C*Int[Csc[e+f*x]*(1+Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*sec[e_.+f_.*x_]^2)/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Int[(A-C*Sec[e+f*x])/Sqrt[a+b*Sec[e+f*x]],x] + C*Int[Sec[e+f*x]*(1+Sec[e+f*x])/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_+C_.*csc[e_.+f_.*x_]^2)/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Int[(A-C*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] + C*Int[Csc[e+f*x]*(1+Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*
    Simp[A*(a^2-b^2)*(m+1)-a*(A*b-a*B+b*C)*(m+1)*Sec[e+f*x]+(A*b^2-a*b*B+a^2*C)*(m+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && IntegerQ[2*m] && m<-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*
    Simp[A*(a^2-b^2)*(m+1)-a*(A*b-a*B+b*C)*(m+1)*Csc[e+f*x]+(A*b^2-a*b*B+a^2*C)*(m+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*
    Simp[A*(a^2-b^2)*(m+1)-a*b*(A+C)*(m+1)*Sec[e+f*x]+(A*b^2+a^2*C)*(m+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2] && IntegerQ[2*m] && m<-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*
    Simp[A*(a^2-b^2)*(m+1)-a*b*(A+C)*(m+1)*Csc[e+f*x]+(A*b^2+a^2*C)*(m+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2] && IntegerQ[2*m] && m<-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  1/b*Int[(a+b*Sec[e+f*x])^m*(A*b+(b*B-a*C)*Sec[e+f*x]),x] + C/b*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*m]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  1/b*Int[(a+b*Csc[e+f*x])^m*(A*b+(b*B-a*C)*Csc[e+f*x]),x] + C/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*m]]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  1/b*Int[(a+b*Sec[e+f*x])^m*(A*b-a*C*Sec[e+f*x]),x] + C/b*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*m]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  1/b*Int[(a+b*Csc[e+f*x])^m*(A*b-a*C*Csc[e+f*x]),x] + C/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && Not[IntegerQ[2*m]]


(* ::Subsection::Closed:: *)
(*6 (a+b sec)^m (d sec)^n (A+B sec+C sec^2)*)


Int[(a_+b_.*sec[e_.+f_.*x_])*(d_.*sec[e_.+f_.*x_])^n_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*a*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Sec[e+f*x])^(n+1)*Simp[n*(B*a+A*b)+(n*(a*C+B*b)+A*a*(n+1))*Sec[e+f*x]+b*C*n*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && RationalQ[n] && n<-1


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Csc[e+f*x])^(n+1)*Simp[n*(B*a+A*b)+(n*(a*C+B*b)+A*a*(n+1))*Csc[e+f*x]+b*C*n*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && RationalQ[n] && n<-1


Int[(a_+b_.*sec[e_.+f_.*x_])*(d_.*sec[e_.+f_.*x_])^n_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*a*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Sec[e+f*x])^(n+1)*Simp[A*b*n+a*(C*n+A*(n+1))*Sec[e+f*x]+b*C*n*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && RationalQ[n] && n<-1


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Csc[e+f*x])^(n+1)*Simp[A*b*n+a*(C*n+A*(n+1))*Csc[e+f*x]+b*C*n*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && RationalQ[n] && n<-1


Int[(d_.*sec[e_.+f_.*x_])^n_.*(a_+b_.*sec[e_.+f_.*x_])*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  b*C*Sec[e+f*x]*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*(n+2)) + 
  1/(n+2)*Int[(d*Sec[e+f*x])^n*Simp[A*a*(n+2)+(B*a*(n+2)+b*(C*(n+1)+A*(n+2)))*Sec[e+f*x]+(a*C+B*b)*(n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && Not[RationalQ[n] && n<-1]


Int[(d_.*csc[e_.+f_.*x_])^n_.*(a_+b_.*csc[e_.+f_.*x_])*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Csc[e+f*x]*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(n+2)) + 
  1/(n+2)*Int[(d*Csc[e+f*x])^n*Simp[A*a*(n+2)+(B*a*(n+2)+b*(C*(n+1)+A*(n+2)))*Csc[e+f*x]+(a*C+B*b)*(n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && Not[RationalQ[n] && n<-1]


Int[(d_.*sec[e_.+f_.*x_])^n_.*(a_+b_.*sec[e_.+f_.*x_])*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  b*C*Sec[e+f*x]*Tan[e+f*x]*(d*Sec[e+f*x])^n/(f*(n+2)) + 
  1/(n+2)*Int[(d*Sec[e+f*x])^n*Simp[A*a*(n+2)+b*(C*(n+1)+A*(n+2))*Sec[e+f*x]+a*C*(n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && Not[RationalQ[n] && n<-1]


Int[(d_.*csc[e_.+f_.*x_])^n_.*(a_+b_.*csc[e_.+f_.*x_])*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Csc[e+f*x]*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(n+2)) + 
  1/(n+2)*Int[(d*Csc[e+f*x])^n*Simp[A*a*(n+2)+b*(C*(n+1)+A*(n+2))*Csc[e+f*x]+a*C*(n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && Not[RationalQ[n] && n<-1]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*Simp[b*A*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Sec[e+f*x],x]*(a+b*Sec[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-2


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*Simp[b*A*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Csc[e+f*x],x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-2


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*Simp[b*A*(m+2)+b*C*(m+1)-a*C*Sec[e+f*x],x]*(a+b*Sec[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-2


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*Simp[b*A*(m+2)+b*C*(m+1)-a*C*Csc[e+f*x],x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-2


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A-b*B+a*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n*
    Simp[a*B*n-b*C*n-A*b*(2*m+n+1)-(b*B*(m+n+1)-a*(A*(m+n+1)-C*(m-n)))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A-b*B+a*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[a*B*n-b*C*n-A*b*(2*m+n+1)-(b*B*(m+n+1)-a*(A*(m+n+1)-C*(m-n)))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A+C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n*
    Simp[b*C*n+A*b*(2*m+n+1)-(a*(A*(m+n+1)-C*(m-n)))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A+C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[b*C*n+A*b*(2*m+n+1)-(a*(A*(m+n+1)-C*(m-n)))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1)*Simp[a*A*m-b*B*n-b*(A*(m+n+1)+C*n)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && (RationalQ[n] && n<-1/2 || ZeroQ[m+n+1])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*Simp[a*A*m-b*B*n-b*(A*(m+n+1)+C*n)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && (RationalQ[n] && n<-1/2 || ZeroQ[m+n+1])


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1)*Simp[a*A*m-b*(A*(m+n+1)+C*n)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && (RationalQ[n] && n<-1/2 || ZeroQ[m+n+1])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*Simp[a*A*m-b*(A*(m+n+1)+C*n)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && (RationalQ[n] && n<-1/2 || ZeroQ[m+n+1])


Int[sec[e_.+f_.*x_]*(A_+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2)*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*Simp[b*A*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Sec[e+f*x],x]*(a+b*Sec[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-2


Int[csc[e_.+f_.*x_]*(A_+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*Simp[b*A*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Csc[e+f*x],x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-2


Int[sec[e_.+f_.*x_]*(A_+C_.*sec[e_.+f_.*x_]^2)*(a_+b_.*sec[e_.+f_.*x_])^m_,x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*Simp[b*A*(m+2)+b*C*(m+1)-a*C*Sec[e+f*x],x]*(a+b*Sec[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-2


Int[csc[e_.+f_.*x_]*(A_+C_.*csc[e_.+f_.*x_]^2)*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*Simp[b*A*(m+2)+b*C*(m+1)-a*C*Csc[e+f*x],x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[m] && m>-2


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n*Simp[A*b*(m+n+1)+b*C*n+(a*C*m+b*B*(m+n+1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && NonzeroQ[m+n+1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*Simp[A*b*(m+n+1)+b*C*n+(a*C*m+b*B*(m+n+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && NonzeroQ[m+n+1]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n*Simp[A*b*(m+n+1)+b*C*n+a*C*m*Sec[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,m,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && NonzeroQ[m+n+1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*Simp[A*b*(m+n+1)+b*C*n+a*C*m*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,m,n},x] && ZeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && NonzeroQ[m+n+1]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*
    Simp[b*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(m+1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[b*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*
    Simp[a*b*(A+C)*(m+1)-(A*b^2+a^2*C+b*(A*b+b*C)*(m+1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[a*b*(A+C)*(m+1)-(A*b^2+a^2*C+b*(A*b+b*C)*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m*Simp[b*A*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*Simp[b*A*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[sec[e_.+f_.*x_]*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m*Simp[b*A*(m+2)+b*C*(m+1)-a*C*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*Simp[b*A*(m+2)+b*C*(m+1)-a*C*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A*b^2-a*b*B+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*
    Simp[b*(m+1)*(-a*(b*B-a*C)+A*b^2)+
      (b*B*(a^2+b^2*(m+1))-a*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Sec[e+f*x]-
      b*C*(m+1)*(a^2-b^2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[b*(m+1)*(-a*(b*B-a*C)+A*b^2)+
      (b*B*(a^2+b^2*(m+1))-a*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Csc[e+f*x]-
      b*C*(m+1)*(a^2-b^2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A*b^2+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*
    Simp[b*(m+1)*(a^2*C+A*b^2)-a*(A*b^2*(m+2)+C*(a^2+b^2*(m+1)))*Sec[e+f*x]-b*C*(m+1)*(a^2-b^2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[b*(m+1)*(a^2*C+A*b^2)-a*(A*b^2*(m+2)+C*(a^2+b^2*(m+1)))*Csc[e+f*x]-b*C*(m+1)*(a^2-b^2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sec[e+f*x]*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m*
    Simp[a*C+b*(C*(m+2)+A*(m+3))*Sec[e+f*x]-(2*a*C-b*B*(m+3))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Csc[e+f*x]*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*
    Simp[a*C+b*(C*(m+2)+A*(m+3))*Csc[e+f*x]-(2*a*C-b*B*(m+3))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[sec[e_.+f_.*x_]^2*(a_+b_.*sec[e_.+f_.*x_])^m_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Sec[e+f*x]*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m*Simp[a*C+b*(C*(m+2)+A*(m+3))*Sec[e+f*x]-2*a*C*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Csc[e+f*x]*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*Simp[a*C+b*(C*(m+2)+A*(m+3))*Csc[e+f*x]-2*a*C*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n+1)*
    Simp[A*b*m-a*B*n-(b*B*n+a*(C*n+A*(n+1)))*Sec[e+f*x]-b*(C*n+A*(m+n+1))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>0 && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1)*
    Simp[A*b*m-a*B*n-(b*B*n+a*(C*n+A*(n+1)))*Csc[e+f*x]-b*(C*n+A*(m+n+1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>0 && n<=-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^(n+1)*
    Simp[A*b*m-a*(C*n+A*(n+1))*Sec[e+f*x]-b*(C*n+A*(m+n+1))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>0 && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1)*
    Simp[A*b*m-a*(C*n+A*(n+1))*Csc[e+f*x]-b*(C*n+A*(m+n+1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m>0 && n<=-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*(m+n+1)) + 
  1/(m+n+1)*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n*
    Simp[a*A*(m+n+1)+a*C*n+((A*b+a*B)*(m+n+1)+b*C*(m+n))*Sec[e+f*x]+(b*B*(m+n+1)+a*C*m)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[n] && n<=-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+n+1)) + 
  1/(m+n+1)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n*
    Simp[a*A*(m+n+1)+a*C*n+((A*b+a*B)*(m+n+1)+b*C*(m+n))*Csc[e+f*x]+(b*B*(m+n+1)+a*C*m)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[n] && n<=-1]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*Tan[e+f*x]*(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n/(f*(m+n+1)) + 
  1/(m+n+1)*Int[(a+b*Sec[e+f*x])^(m-1)*(d*Sec[e+f*x])^n*
    Simp[a*A*(m+n+1)+a*C*n+b*(A*(m+n+1)+C*(m+n))*Sec[e+f*x]+a*C*m*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[n] && n<=-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+n+1)) + 
  1/(m+n+1)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n*
    Simp[a*A*(m+n+1)+a*C*n+b*(A*(m+n+1)+C*(m+n))*Csc[e+f*x]+a*C*m*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[n] && n<=-1]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  d*(A*b^2-a*b*B+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)/(b*f*(a^2-b^2)*(m+1)) + 
  d/(b*(a^2-b^2)*(m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)*
    Simp[A*b^2*(n-1)-a*(b*B-a*C)*(n-1)+
      b*(a*A-b*B+a*C)*(m+1)*Sec[e+f*x]-
      (b*(A*b-a*B)*(m+n+1)+C*(a^2*n+b^2*(m+1)))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -d*(A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(b*f*(a^2-b^2)*(m+1)) + 
  d/(b*(a^2-b^2)*(m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[A*b^2*(n-1)-a*(b*B-a*C)*(n-1)+
      b*(a*A-b*B+a*C)*(m+1)*Csc[e+f*x]-
      (b*(A*b-a*B)*(m+n+1)+C*(a^2*n+b^2*(m+1)))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  d*(A*b^2+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)/(b*f*(a^2-b^2)*(m+1)) + 
  d/(b*(a^2-b^2)*(m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)*
    Simp[A*b^2*(n-1)+a^2*C*(n-1)+a*b*(A+C)*(m+1)*Sec[e+f*x]-(A*b^2*(m+n+1)+C*(a^2*n+b^2*(m+1)))*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -d*(A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(b*f*(a^2-b^2)*(m+1)) + 
  d/(b*(a^2-b^2)*(m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[A*b^2*(n-1)+a^2*C*(n-1)+a*b*(A+C)*(m+1)*Csc[e+f*x]-(A*b^2*(m+n+1)+C*(a^2*n+b^2*(m+1)))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n*
    Simp[a*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C)*(m+n+1)-
      a*(A*b-a*B+b*C)*(m+1)*Sec[e+f*x]+
      (A*b^2-a*b*B+a^2*C)*(m+n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[a*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C)*(m+n+1)-
      a*(A*b-a*B+b*C)*(m+1)*Csc[e+f*x]+
      (A*b^2-a*b*B+a^2*C)*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n*
    Simp[a^2*(A+C)*(m+1)-(A*b^2+a^2*C)*(m+n+1)-a*b*(A+C)*(m+1)*Sec[e+f*x]+(A*b^2+a^2*C)*(m+n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[a^2*(A+C)*(m+1)-(A*b^2+a^2*C)*(m+n+1)-a*b*(A+C)*(m+1)*Csc[e+f*x]+(A*b^2+a^2*C)*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)/(b*f*(m+n+1)) + 
  d/(b*(m+n+1))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)*
    Simp[a*C*(n-1)+(A*b*(m+n+1)+b*C*(m+n))*Sec[e+f*x]+(b*B*(m+n+1)-a*C*n)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 (* && Not[IntegerQ[m] && m>0 && Not[IntegerQ[n]]] *)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(b*f*(m+n+1)) + 
  d/(b*(m+n+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)*
    Simp[a*C*(n-1)+(A*b*(m+n+1)+b*C*(m+n))*Csc[e+f*x]+(b*B*(m+n+1)-a*C*n)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 (* && Not[IntegerQ[m] && m>0 && Not[IntegerQ[n]]] *)


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  C*d*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^(n-1)/(b*f*(m+n+1)) + 
  d/(b*(m+n+1))*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n-1)*
    Simp[a*C*(n-1)+(A*b*(m+n+1)+b*C*(m+n))*Sec[e+f*x]-a*C*n*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 (* && Not[IntegerQ[m] && m>0 && Not[IntegerQ[n]]] *)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(b*f*(m+n+1)) + 
  d/(b*(m+n+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)*
    Simp[a*C*(n-1)+(A*b*(m+n+1)+b*C*(m+n))*Csc[e+f*x]-a*C*n*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>0 (* && Not[IntegerQ[m] && m>0 && Not[IntegerQ[n]]] *)


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1)*
    Simp[a*B*n-A*b*(m+n+1)+a*(A+A*n+C*n)*Sec[e+f*x]+A*b*(m+n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*
    Simp[a*B*n-A*b*(m+n+1)+a*(A+A*n+C*n)*Csc[e+f*x]+A*b*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  -A*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m+1)*(d*Sec[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n+1)*
    Simp[-A*b*(m+n+1)+a*(A+A*n+C*n)*Sec[e+f*x]+A*b*(m+n+2)*Sec[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*
    Simp[-A*b*(m+n+1)+a*(A+A*n+C*n)*Csc[e+f*x]+A*b*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2)/(Sqrt[d_.*sec[e_.+f_.*x_]]*(a_+b_.*sec[e_.+f_.*x_])),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)/(a^2*d^2)*Int[(d*Sec[e+f*x])^(3/2)/(a+b*Sec[e+f*x]),x] + 
  1/a^2*Int[(a*A-(A*b-a*B)*Sec[e+f*x])/Sqrt[d*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)/(Sqrt[d_.*csc[e_.+f_.*x_]]*(a_+b_.*csc[e_.+f_.*x_])),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)/(a^2*d^2)*Int[(d*Csc[e+f*x])^(3/2)/(a+b*Csc[e+f*x]),x] + 
  1/a^2*Int[(a*A-(A*b-a*B)*Csc[e+f*x])/Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+C_.*sec[e_.+f_.*x_]^2)/(Sqrt[d_.*sec[e_.+f_.*x_]]*(a_+b_.*sec[e_.+f_.*x_])),x_Symbol] :=
  (A*b^2+a^2*C)/(a^2*d^2)*Int[(d*Sec[e+f*x])^(3/2)/(a+b*Sec[e+f*x]),x] + 
  1/a^2*Int[(a*A-A*b*Sec[e+f*x])/Sqrt[d*Sec[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+C_.*csc[e_.+f_.*x_]^2)/(Sqrt[d_.*csc[e_.+f_.*x_]]*(a_+b_.*csc[e_.+f_.*x_])),x_Symbol] :=
  (A*b^2+a^2*C)/(a^2*d^2)*Int[(d*Csc[e+f*x])^(3/2)/(a+b*Csc[e+f*x]),x] + 
  1/a^2*Int[(a*A-A*b*Csc[e+f*x])/Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2)/(Sqrt[d_.*sec[e_.+f_.*x_]]*Sqrt[a_+b_.*sec[e_.+f_.*x_]]),x_Symbol] :=
  C/d^2*Int[(d*Sec[e+f*x])^(3/2)/Sqrt[a+b*Sec[e+f*x]],x] + 
  Int[(A+B*Sec[e+f*x])/(Sqrt[d*Sec[e+f*x]]*Sqrt[a+b*Sec[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)/(Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  C/d^2*Int[(d*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] + 
  Int[(A+B*Csc[e+f*x])/(Sqrt[d*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+C_.*sec[e_.+f_.*x_]^2)/(Sqrt[d_.*sec[e_.+f_.*x_]]*Sqrt[a_+b_.*sec[e_.+f_.*x_]]),x_Symbol] :=
  C/d^2*Int[(d*Sec[e+f*x])^(3/2)/Sqrt[a+b*Sec[e+f*x]],x] + 
  A*Int[1/(Sqrt[d*Sec[e+f*x]]*Sqrt[a+b*Sec[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2]


Int[(A_.+C_.*csc[e_.+f_.*x_]^2)/(Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  C/d^2*Int[(d*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] + 
  A*Int[1/(Sqrt[d*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n*(A+B*Sec[e+f*x]+C*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,B,C,m,n},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*(A+B*Csc[e+f*x]+C*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,B,C,m,n},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(d_.*sec[e_.+f_.*x_])^n_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^n*(A+C*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,C,m,n},x] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*(A+C*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,C,m,n},x] && NonzeroQ[a^2-b^2]


(* ::Subsection::Closed:: *)
(*7 (e trig)^m (a+b sec)^n*)


(* Int[sin[c_.+d_.*x_]^m_.*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  -1/d*Subst[Int[(1-x^2)^((m-1)/2)*(b+a*x)^n/x^n,x],x,Cos[c+d*x]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && IntegerQ[n] *)


(* Int[cos[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(1-x^2)^((m-1)/2)*(b+a*x)^n/x^n,x],x,Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] && OddQ[m] && IntegerQ[n] *)


Int[(e_.*sin[c_.+d_.*x_])^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  e*(e*Sin[c+d*x])^(m-1)/(b*d*(m-1)) - e^2/a*Int[Cos[c+d*x]^2*(e*Sin[c+d*x])^(m-2),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m-1]


Int[(e_.*cos[c_.+d_.*x_])^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -e*(e*Cos[c+d*x])^(m-1)/(b*d*(m-1)) - e^2/a*Int[Sin[c+d*x]^2*(e*Cos[c+d*x])^(m-2),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[a^2-b^2] && NonzeroQ[m-1]


Int[sin[c_.+d_.*x_]^m_./(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -1/d*Subst[Int[x*(1-x^2)^((m-1)/2)/(b+a*x),x],x,Cos[c+d*x]] /;
FreeQ[{a,b,c,d},x] (* && NonzeroQ[a^2-b^2] *) && OddQ[m]


Int[cos[c_.+d_.*x_]^m_./(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  1/d*Subst[Int[x*(1-x^2)^((m-1)/2)/(b+a*x),x],x,Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] (* && NonzeroQ[a^2-b^2] *) && OddQ[m]


Int[(e_.*sin[c_.+d_.*x_])^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  b*e*(e*Sin[c+d*x])^(m-1)/(d*a^2*(m-1)) - 
  e^2/a*Int[Cos[c+d*x]^2*(e*Sin[c+d*x])^(m-2),x] + 
  e^2*(a^2-b^2)/a^2*Int[(e*Sin[c+d*x])^(m-2)/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m>1


Int[(e_.*cos[c_.+d_.*x_])^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -b*e*(e*Cos[c+d*x])^(m-1)/(d*a^2*(m-1)) - 
  e^2/a*Int[Sin[c+d*x]^2*(e*Cos[c+d*x])^(m-2),x] + 
  e^2*(a^2-b^2)/a^2*Int[(e*Cos[c+d*x])^(m-2)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m>1


Int[(e_.*sin[c_.+d_.*x_])^m_/(a_+b_.*sec[c_.+d_.*x_]),x_Symbol] :=
  -b*(e*Sin[c+d*x])^(m+1)/(d*e*(m+1)*(a^2-b^2)) + 
  a/(a^2-b^2)*Int[Cos[c+d*x]^2*(e*Sin[c+d*x])^m,x] + 
  a^2/(e^2*(a^2-b^2))*Int[(e*Sin[c+d*x])^(m+2)/(a+b*Sec[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m<-1


Int[(e_.*cos[c_.+d_.*x_])^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  b*(e*Cos[c+d*x])^(m+1)/(d*e*(m+1)*(a^2-b^2)) + 
  a/(a^2-b^2)*Int[Sin[c+d*x]^2*(e*Cos[c+d*x])^m,x] + 
  a^2/(e^2*(a^2-b^2))*Int[(e*Cos[c+d*x])^(m+2)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2] && Not[OddQ[m]] && RationalQ[m] && m<-1


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
(*8 (a+b sec)^m (c+d sec)^n*)


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


Int[(A_+B_.*sec[e_.+f_.*x_])/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  A*x/a - (A*b-a*B)/a*Int[Sec[e+f*x]/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B]


Int[(A_+B_.*csc[e_.+f_.*x_])/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*x/a - (A*b-a*B)/a*Int[Csc[e+f*x]/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  A*Int[Sqrt[a+b*Sec[e+f*x]],x] + B*Int[Sec[e+f*x]*Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Int[Sqrt[a+b*Csc[e+f*x]],x] + B*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  b*B*Tan[e+f*x]*(a+b*Sec[e+f*x])^(m-1)/(f*m) + 
  1/m*Int[(a+b*Sec[e+f*x])^(m-1)*Simp[a*A*m+(A*b*m+a*B*(2*m-1))*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2 && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)/(f*m) + 
  1/m*Int[(a+b*Csc[e+f*x])^(m-1)*Simp[a*A*m+(A*b*m+a*B*(2*m-1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m>1/2 && IntegerQ[2*m]


Int[(A_+B_.*sec[e_.+f_.*x_])/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  A/a*Int[Sqrt[a+b*Sec[e+f*x]],x] - (A*b-a*B)/a*Int[Sec[e+f*x]/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(A_+B_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  A/a*Int[Sqrt[a+b*Csc[e+f*x]],x] - (A*b-a*B)/a*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Tan[e+f*x]*(a+b*Sec[e+f*x])^m/(b*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Sec[e+f*x])^(m+1)*Simp[a*A*(2*m+1)-(A*b-a*B)*(m+1)*Sec[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2 && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(b*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*Simp[a*A*(2*m+1)-(A*b-a*B)*(m+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && ZeroQ[a^2-b^2] && RationalQ[m] && m<-1/2 && IntegerQ[2*m]


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^m_,x_Symbol] :=
  b*B*Tan[c+d*x]*(a+b*Sec[c+d*x])^(m-1)/(d*m) + 
  1/m*Int[(a+b*Sec[c+d*x])^(m-2)*
    Simp[a^2*A*m+(b^2*B*(m-1)+2*a*A*b*m+a^2*B*m)*Sec[c+d*x]+b*(A*b*m+a*B*(2*m-1))*Sec[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^m_,x_Symbol] :=
  -b*B*Cot[c+d*x]*(a+b*Csc[c+d*x])^(m-1)/(d*m) + 
  1/m*Int[(a+b*Csc[c+d*x])^(m-2)*
    Simp[a^2*A*m+(b^2*B*(m-1)+2*a*A*b*m+a^2*B*m)*Csc[c+d*x]+b*(A*b*m+a*B*(2*m-1))*Csc[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>1


Int[(A_+B_.*sec[c_.+d_.*x_])*(a_+b_.*sec[c_.+d_.*x_])^m_,x_Symbol] :=
  -b*(A*b-a*B)*Tan[c+d*x]*(a+b*Sec[c+d*x])^(m+1)/(a*d*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Sec[c+d*x])^(m+1)*
    Simp[A*(a^2-b^2)*(m+1)-(a*(A*b-a*B)*(m+1))*Sec[c+d*x]+b*(A*b-a*B)*(m+2)*Sec[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(A_+B_.*csc[c_.+d_.*x_])*(a_+b_.*csc[c_.+d_.*x_])^m_,x_Symbol] :=
  b*(A*b-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(m+1)/(a*d*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[c+d*x])^(m+1)*
    Simp[A*(a^2-b^2)*(m+1)-(a*(A*b-a*B)*(m+1))*Csc[c+d*x]+b*(A*b-a*B)*(m+2)*Csc[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(A_+B_.*sec[e_.+f_.*x_])/Sqrt[a_+b_.*sec[e_.+f_.*x_]],x_Symbol] :=
  A*Int[1/Sqrt[a+b*Sec[e+f*x]],x] + B*Int[Sec[e+f*x]/Sqrt[a+b*Sec[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(A_+B_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  A*Int[1/Sqrt[a+b*Csc[e+f*x]],x] + B*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B},x] && NonzeroQ[A*b-a*B] && NonzeroQ[a^2-b^2]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_*(A_+B_.*sec[e_.+f_.*x_]),x_Symbol] :=
  A*Int[(a+b*Sec[e+f*x])^m,x] + B*Int[Sec[e+f*x]*(a+b*Sec[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,B,m},x] && NonzeroQ[A*b-a*B]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Int[(a+b*Csc[e+f*x])^m,x] + B*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,A,B,m},x] && NonzeroQ[A*b-a*B]


Int[Sqrt[c_+d_.*sec[e_.+f_.*x_]]/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  c/a*Int[1/Sqrt[c+d*Sec[e+f*x]],x] - 
  (b*c-a*d)/a*Int[Sec[e+f*x]/((a+b*Sec[e+f*x])*Sqrt[c+d*Sec[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[c_+d_.*csc[e_.+f_.*x_]]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  c/a*Int[1/Sqrt[c+d*Csc[e+f*x]],x] - 
  (b*c-a*d)/a*Int[Csc[e+f*x]/((a+b*Csc[e+f*x])*Sqrt[c+d*Csc[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(c_+d_.*sec[e_.+f_.*x_])^(3/2)/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[Sqrt[c+d*Sec[e+f*x]],x] + (b*c-a*d)/b*Int[Sqrt[c+d*Sec[e+f*x]]/(a+b*Sec[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(c_+d_.*csc[e_.+f_.*x_])^(3/2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[Sqrt[c+d*Csc[e+f*x]],x] + (b*c-a*d)/b*Int[Sqrt[c+d*Csc[e+f*x]]/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[1/((a_+b_.*sec[e_.+f_.*x_])*Sqrt[c_+d_.*sec[e_.+f_.*x_]]),x_Symbol] :=
  1/a*Int[1/Sqrt[c+d*Sec[e+f*x]],x] - 
  b/a*Int[Sec[e+f*x]/((a+b*Sec[e+f*x])*Sqrt[c+d*Sec[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[1/((a_+b_.*csc[e_.+f_.*x_])*Sqrt[c_+d_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  1/a*Int[1/Sqrt[c+d*Csc[e+f*x]],x] - 
  b/a*Int[Csc[e+f*x]/((a+b*Csc[e+f*x])*Sqrt[c+d*Csc[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]/Sqrt[c_+d_.*sec[e_.+f_.*x_]],x_Symbol] :=
  -2*(a+b*Sec[e+f*x])/(c*f*Rt[(a+b)/(c+d),2]*Tan[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Sec[e+f*x])/((c-d)*(a+b*Sec[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Sec[e+f*x])/((c+d)*(a+b*Sec[e+f*x]))]*
    EllipticPi[a*(c+d)/(c*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sec[e+f*x]]/Sqrt[a+b*Sec[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PosQ[(a+b)/(c+d)]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  2*(a+b*Csc[e+f*x])/(c*f*Rt[(a+b)/(c+d),2]*Cot[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Csc[e+f*x])/((c-d)*(a+b*Csc[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Csc[e+f*x])/((c+d)*(a+b*Csc[e+f*x]))]*
    EllipticPi[a*(c+d)/(c*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && PosQ[(a+b)/(c+d)]


Int[Sqrt[a_+b_.*sec[e_.+f_.*x_]]/Sqrt[c_+d_.*sec[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[-c-d*Sec[e+f*x]]/Sqrt[c+d*Sec[e+f*x]]*Int[Sqrt[a+b*Sec[e+f*x]]/Sqrt[-c-d*Sec[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NegQ[(a+b)/(c+d)]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[-c-d*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]]*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[-c-d*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2] && NegQ[(a+b)/(c+d)]


Int[1/(Sqrt[a_+b_.*sec[e_.+f_.*x_]]*Sqrt[c_+d_.*sec[e_.+f_.*x_]]),x_Symbol] :=
  -b/a*Int[Sec[e+f*x]/(Sqrt[a+b*Sec[e+f*x]]*Sqrt[c+d*Sec[e+f*x]]),x] + 
  1/a*Int[Sqrt[a+b*Sec[e+f*x]]/Sqrt[c+d*Sec[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[1/(Sqrt[a_+b_.*cos[e_.+f_.*x_]]*Sqrt[c_+d_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  -b/a*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]]),x] + 
  1/a*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(g_.*sec[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sec[e_.+f_.*x_]]/(a_+b_.*sec[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[(g*Sec[e+f*x])^(3/2)/Sqrt[c+d*Sec[e+f*x]],x] + 
  (b*c-a*d)/b*Int[(g*Sec[e+f*x])^(3/2)/((a+b*Sec[e+f*x])*Sqrt[c+d*Sec[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(g_.*csc[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*csc[e_.+f_.*x_]]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[(g*Csc[e+f*x])^(3/2)/Sqrt[c+d*Csc[e+f*x]],x] + 
  (b*c-a*d)/b*Int[(g*Csc[e+f*x])^(3/2)/((a+b*Csc[e+f*x])*Sqrt[c+d*Csc[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(g_.*sec[e_.+f_.*x_])^(3/2)/((a_+b_.*sec[e_.+f_.*x_])*Sqrt[c_+d_.*sec[e_.+f_.*x_]]),x_Symbol] :=
  2*g*Sqrt[g*Sec[e+f*x]]*Sqrt[Sec[e+f*x]]*Sqrt[-1+Sec[e+f*x]]/(f*(a+b)*Tan[e+f*x]*Sqrt[c+d*Sec[e+f*x]])*
    Sqrt[(1+Sec[e+f*x])/Sec[e+f*x]]*Sqrt[(c+d*Sec[e+f*x])/((c+d)*Sec[e+f*x])]*
    EllipticPi[2*a/(a+b),ArcSin[Sqrt[-1+Sec[e+f*x]]/(Sqrt[2]*Sqrt[Sec[e+f*x]])],2*c/(c+d)] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


Int[(g_.*csc[e_.+f_.*x_])^(3/2)/((a_+b_.*csc[e_.+f_.*x_])*Sqrt[c_+d_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  -2*g*Sqrt[g*Csc[e+f*x]]*Sqrt[Csc[e+f*x]]*Sqrt[-1+Csc[e+f*x]]/(f*(a+b)*Cot[e+f*x]*Sqrt[c+d*Csc[e+f*x]])*
    Sqrt[(1+Csc[e+f*x])/Csc[e+f*x]]*Sqrt[(c+d*Csc[e+f*x])/((c+d)*Csc[e+f*x])]*
    EllipticPi[2*a/(a+b),ArcSin[Sqrt[-1+Csc[e+f*x]]/(Sqrt[2]*Sqrt[Csc[e+f*x]])],2*c/(c+d)] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a^2-b^2] && NonzeroQ[c^2-d^2]


(* ::Subsection::Closed:: *)
(*9 trig^m (a+b sec^n)^p*)


Int[(a_+b_.*sec[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Int[(-a*Tan[c+d*x]^2)^p,x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[a+b]


Int[(a_+b_.*csc[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  Int[(-a*Cot[c+d*x]^2)^p,x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[a+b]


Int[1/(a_+b_.*sec[c_.+d_.*x_]^2),x_Symbol] :=
  x/a - b/a*Int[1/(b+a*Cos[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b]


Int[1/(a_+b_.*csc[c_.+d_.*x_]^2),x_Symbol] :=
  x/a - b/a*Int[1/(b+a*Sin[c+d*x]^2),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b]


Int[(a_+b_.*sec[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  1/d*Subst[Int[(a+b+b*x^2)^p/(1+x^2),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[a+b] && NonzeroQ[p+1]


Int[(a_+b_.*csc[c_.+d_.*x_]^2)^p_,x_Symbol] :=
  -1/d*Subst[Int[(a+b+b*x^2)^p/(1+x^2),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d,p},x] && NonzeroQ[a+b] && NonzeroQ[p+1]


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


(* ::Subsection::Closed:: *)
(*10 trig^m (a+b sec^n+c sec^(2 n))^p*)


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
(*11 Secant normalization rules*)


Int[u_*(c_.*sin[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Sin[a+b*x])^m*(d*Csc[a+b*x])^m*Int[ActivateTrig[u]*(d*Csc[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*cos[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cos[a+b*x])^m*(d*Sec[a+b*x])^m*Int[ActivateTrig[u]*(d*Sec[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^m*Int[ActivateTrig[u]*(d*Sec[a+b*x])^(m+n)/(d*Csc[a+b*x])^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^m*Int[ActivateTrig[u]*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^m*Int[ActivateTrig[u]*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^m*Int[ActivateTrig[u]*(d*Csc[a+b*x])^(m+n)/(d*Sec[a+b*x])^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*sin[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Csc[a+b*x])^m*(c*Sin[a+b*x])^m*Int[ActivateTrig[u]/(c*Csc[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*cos[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cos[a+b*x])^m*(c*Sec[a+b*x])^m*Int[ActivateTrig[u]/(c*Sec[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(c*Csc[a+b*x])^m/(c*Sec[a+b*x])^m*Int[ActivateTrig[u]*(c*Sec[a+b*x])^m/(c*Csc[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(c*Sec[a+b*x])^m/(c*Csc[a+b*x])^m*Int[ActivateTrig[u]*(c*Csc[a+b*x])^m/(c*Sec[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*sec[a_.+b_.*x_])^n_.*(A_+B_.*cos[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-1)*(B+A*Sec[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*csc[a_.+b_.*x_])^n_.*(A_+B_.*sin[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-1)*(B+A*Csc[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_+B_.*cos[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Sec[a+b*x])/Sec[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_+B_.*sin[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Csc[a+b*x])/Csc[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownSecantIntegrandQ[u,x]


Int[u_.*(c_.*sec[a_.+b_.*x_])^n_.*(A_.+B_.*cos[a_.+b_.*x_]+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-2)*(C+B*Sec[a+b*x]+A*Sec[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_.*(c_.*csc[a_.+b_.*x_])^n_.*(A_.+B_.*sin[a_.+b_.*x_]+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-2)*(C+B*Csc[a+b*x]+A*Csc[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_.*(c_.*sec[a_.+b_.*x_])^n_.*(A_+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-2)*(C+A*Sec[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_.*(c_.*csc[a_.+b_.*x_])^n_.*(A_+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-2)*(C+A*Csc[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_.+B_.*cos[a_.+b_.*x_]+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Sec[a+b*x]+A*Sec[a+b*x]^2)/Sec[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_.+B_.*sin[a_.+b_.*x_]+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Csc[a+b*x]+A*Csc[a+b*x]^2)/Csc[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Sec[a+b*x]^2)/Sec[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Csc[a+b*x]^2)/Csc[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_.*sec[a_.+b_.*x_]^n_.+B_.*sec[a_.+b_.*x_]^n1_+C_.*sec[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Sec[a+b*x]^n*(A+B*Sec[a+b*x]+C*Sec[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && ZeroQ[n1-n-1] && ZeroQ[n2-n-2]


Int[u_*(A_.*csc[a_.+b_.*x_]^n_.+B_.*csc[a_.+b_.*x_]^n1_+C_.*csc[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Csc[a+b*x]^n*(A+B*Csc[a+b*x]+C*Csc[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && ZeroQ[n1-n-1] && ZeroQ[n2-n-2]
