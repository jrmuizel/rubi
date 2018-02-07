(* ::Package:: *)

(* ::Section:: *)
(*Inverse Hyperbolic Function Rules*)


(* ::Subsection::Closed:: *)
(*7.1.1 (a+b arcsinh(c x))^n*)


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcSinh[c*x])^n - 
  b*c*n*Int[x*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c},x] && GtQ[n,0]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcCosh[c*x])^n - 
  b*c*n*Int[x*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c},x] && GtQ[n,0]


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  c/(b*(n+1))*Int[x*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c},x] && LtQ[n,-1]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  Sqrt[-1+c*x]*Sqrt[1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) - 
  c/(b*(n+1))*Int[x*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c},x] && LtQ[n,-1]


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  1/(b*c)*Subst[Int[x^n*Cosh[a/b-x/b],x],x,a+b*ArcSinh[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  -1/(b*c)*Subst[Int[x^n*Sinh[a/b-x/b],x],x,a+b*ArcCosh[c*x]] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*7.1.2 (d x)^m (a+b arcsinh(c x))^n*)


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./x_,x_Symbol] :=
  Subst[Int[(a+b*x)^n/Tanh[x],x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c},x] && IGtQ[n,0]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./x_,x_Symbol] :=
  Subst[Int[(a+b*x)^n/Coth[x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c},x] && IGtQ[n,0]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcSinh[c*x])^n/(d*(m+1)) - 
  b*c*n/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCosh[c*x])^n/(d*(m+1)) - 
  b*c*n/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && NeQ[m,-1]


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcSinh[c*x])^n/(m+1) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && GtQ[n,0]


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcCosh[c*x])^n/(m+1) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && GtQ[n,0]


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1),Sinh[x]^(m-1)*(m+(m+1)*Sinh[x]^2),x],x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && GeQ[n,-2] && LtQ[n,-1]


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[-1+c*x]*Sqrt[1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1)*Cosh[x]^(m-1)*(m-(m+1)*Cosh[x]^2),x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && GeQ[n,-2] && LtQ[n,-1]


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] - 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && LtQ[n,-2]


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[-1+c*x]*Sqrt[1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] - 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && LtQ[n,-2]


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Sinh[x]^m*Cosh[x],x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,n},x] && IGtQ[m,0]


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Cosh[x]^m*Sinh[x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,n},x] && IGtQ[m,0]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d*x)^m*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d*x)^m*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]





(* ::Subsection::Closed:: *)
(*7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n*)


Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])),x_Symbol] :=
  Log[a+b*ArcSinh[c*x]]/(b*c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[d,0]


Int[1/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])),x_Symbol] :=
  Log[a+b*ArcCosh[c*x]]/(b*c*Sqrt[-d1*d2]) /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[d1,0] && LtQ[d2,0]


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && GtQ[d,0] && NeQ[n,-1]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  (a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[d1,0] && LtQ[d2,0] && NeQ[n,-1]


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  Sqrt[1+c*x]*Sqrt[-1+c*x]/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x])*Int[(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && Not[GtQ[d1,0] && LtQ[d2,0]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] - 
  b*c*n*d^p/(2*p+1)*Int[x*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d)^p/((2*p+1))*Int[x*(-1+c*x)^(p-1/2)*(1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && IntegerQ[p]


(* Int[(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(2*p+1) + 
  2*d1*d2*p/(2*p+1)*Int[(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^p/((2*p+1))*Int[x*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && GtQ[p,0] && IntegerQ[p-1/2] && (GtQ[d1,0] && LtQ[d2,0]) *)


Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/2 - 
  b*c*n*Sqrt[d+e*x^2]/(2*Sqrt[1+c^2*x^2])*Int[x*(a+b*ArcSinh[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/(2*Sqrt[1+c^2*x^2])*Int[(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0]


Int[Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/2 - 
  b*c*n*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(2*Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[x*(a+b*ArcCosh[c*x])^(n-1),x] - 
  Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(2*Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/((2*p+1)*(1+c^2*x^2)^FracPart[p])*
    Int[x*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0]


Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(2*p+1) + 
  2*d1*d2*p/(2*p+1)*Int[(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^(p-1/2)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/((2*p+1)*Sqrt[1+c*x]*Sqrt[-1+c*x])*
    Int[x*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && GtQ[p,0] && IntegerQ[p-1/2]


Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(2*p+1) + 
  2*d1*d2*p/(2*p+1)*Int[(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/((2*p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[x*(-1+c*x)^(p-1/2)*(1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && GtQ[p,0]


(* Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcSinh[c*x])^n/(d*Sqrt[d+e*x^2]) - 
  b*c*n/Sqrt[d]*Int[x*(a+b*ArcSinh[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[d,0] *)


(* Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./((d1_+e1_.*x_)^(3/2)*(d2_+e2_.*x_)^(3/2)),x_Symbol] :=
  x*(a+b*ArcCosh[c*x])^n/(d1*d2*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]) + 
  b*c*n/Sqrt[-d1*d2]*Int[x*(a+b*ArcCosh[c*x])^(n-1)/(d1*d2+e1*e2*x^2),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && (GtQ[d1,0] && LtQ[d2,0]) *)


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcSinh[c*x])^n/(d*Sqrt[d+e*x^2]) - 
  b*c*n*Sqrt[1+c^2*x^2]/(d*Sqrt[d+e*x^2])*Int[x*(a+b*ArcSinh[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./((d1_+e1_.*x_)^(3/2)*(d2_+e2_.*x_)^(3/2)),x_Symbol] :=
  x*(a+b*ArcCosh[c*x])^n/(d1*d2*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]) + 
  b*c*n*Sqrt[1+c*x]*Sqrt[-1+c*x]/(d1*d2*Sqrt[d1+e1*x]*Sqrt[d2+e2*x])*Int[x*(a+b*ArcCosh[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0]


(* Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] + 
  b*c*n*d^p/(2*(p+1))*Int[x*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d)^p/(2*(p+1))*Int[x*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && IntegerQ[p]


(* Int[(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  -x*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d1*d2*(p+1)) + 
  (2*p+3)/(2*d1*d2*(p+1))*Int[(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^p/(2*(p+1))*Int[x*(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2] && 
  IntegerQ[p+1/2] && (GtQ[d1,0] && LtQ[d2,0]) *)


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*(p+1)*(1+c^2*x^2)^FracPart[p])*
    Int[x*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]


Int[(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  -x*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d1*d2*(p+1)) + 
  (2*p+3)/(2*d1*d2*(p+1))*Int[(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^(p+1/2)*Sqrt[1+c*x]*Sqrt[-1+c*x]/(2*(p+1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x])*
    Int[x*(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2] && IntegerQ[p+1/2]


Int[(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  -x*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d1*d2*(p+1)) + 
  (2*p+3)/(2*d1*d2*(p+1))*Int[(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(2*(p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[x*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/(c*d)*Subst[Int[(a+b*x)^n*Sech[x],x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[n,0]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -1/(c*d)*Subst[Int[(a+b*x)^n*Csch[x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  d^p*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  c*d^p*(2*p+1)/(b*(n+1))*Int[x*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && LtQ[n,-1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  (-d)^p*(-1+c*x)^(p+1/2)*(1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) - 
  c*(-d)^p*(2*p+1)/(b*(n+1))*Int[x*(-1+c*x)^(p-1/2)*(1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IntegerQ[p]


(* Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  (-d1*d2)^p*(-1+c*x)^(p+1/2)*(1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) - 
  c*(-d1*d2)^p*(2*p+1)/(b*(n+1))*Int[x*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && LtQ[n,-1] && IntegerQ[p-1/2] && (GtQ[d1,0] && LtQ[d2,0]) *)


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1+c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  c*(2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*(n+1)*(1+c^2*x^2)^FracPart[p])*
    Int[x*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && LtQ[n,-1]


Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1+c*x]*Sqrt[-1+c*x]*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) - 
  c*(2*p+1)*(-d1*d2)^(p-1/2)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(b*(n+1)*Sqrt[1+c*x]*Sqrt[-1+c*x])*
    Int[x*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && LtQ[n,-1] && IntegerQ[p-1/2]


Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1+c*x]*Sqrt[-1+c*x]*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) - 
  c*(2*p+1)*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(b*(n+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[x*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && LtQ[n,-1]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^p/c*Subst[Int[(a+b*x)^n*Cosh[x]^(2*p+1),x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && IGtQ[2*p,0] && (IntegerQ[p] || GtQ[d,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d)^p/c*Subst[Int[(a+b*x)^n*Sinh[x]^(2*p+1),x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d1*d2)^p/c*Subst[Int[(a+b*x)^n*Sinh[x]^(2*p+1),x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && IGtQ[p+1/2,0] && (GtQ[d1,0] && LtQ[d2,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]*Int[(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && IGtQ[2*p,0] && Not[IntegerQ[p] || GtQ[d,0]]


Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d1*d2)^(p-1/2)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && IGtQ[2*p,0] && Not[GtQ[d1,0] && LtQ[d2,0]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[e,c^2*d] && (IGtQ[p,0] || ILtQ[p+1/2,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d+e,0] && (IGtQ[p,0] || ILtQ[p+1/2,0])


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Sqrt[1-c^2*x^2]/(Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0]) *)


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n,(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NeQ[e,c^2*d] && IntegerQ[p] && (p>0 || IGtQ[n,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n,(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (p>0 || IGtQ[n,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && IntegerQ[p]


Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n,p},x]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^FracPart[p]*(f+g*x)^FracPart[p]/(d*f+e*g*x^2)^FracPart[p]*
    Int[(d*f+e*g*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[e*f+d*g,0] && EqQ[c^2*f^2+g^2,0] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d)^IntPart[p]*(d+e*x^2)^FracPart[p]/((1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[c^2*d+e,0] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n*)


Int[x_*(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Subst[Int[(a+b*x)^n*Tanh[x],x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[n,0]


Int[x_*(a_.+b_.*ArcCosh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Subst[Int[(a+b*x)^n*Coth[x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


(* Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*e*(p+1)) - 
  b*n*d^p/(2*c*(p+1))*Int[(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && NeQ[p,-1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e*(p+1)) - 
  b*n*(-d)^p/(2*c*(p+1))*Int[(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && NeQ[p,-1] && IntegerQ[p]


(* Int[x_*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e1*e2*(p+1)) - 
  b*n*(-d1*d2)^(p-1/2)/(2*c*(p+1))*Int[(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && IntegerQ[p+1/2] && (GtQ[d1,0] && LtQ[d2,0]) *)


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*e*(p+1)) - 
  b*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && NeQ[p,-1]


Int[x_*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e1*e2*(p+1)) - 
  b*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(2*c*(p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && NeQ[p,-1] && IntegerQ[p+1/2]


Int[x_*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e1*e2*(p+1)) - 
  b*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(2*c*(p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && NeQ[p,-1]


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  1/d*Subst[Int[(a+b*x)^n/(Cosh[x]*Sinh[x]),x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[n,0]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  -1/d*Subst[Int[(a+b*x)^n/(Cosh[x]*Sinh[x]),x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(d*f*(m+1)) - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(d*f*(m+1)) + 
  b*c*n*(-d)^p/(f*(m+1))*Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1] && IntegerQ[p]


(* Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d1*d2*f*(m+1)) + 
  b*c*n*(-d1*d2)^p/(f*(m+1))*Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && 
  NeQ[m,-1] && IntegerQ[p+1/2] && (GtQ[d1,0] && LtQ[d2,0]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(d*f*(m+1)) - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d1*d2*f*(m+1)) + 
  b*c*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(f*(m+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1] && IntegerQ[p+1/2]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d1*d2*f*(m+1)) + 
  b*c*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(f*(m+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])/x_,x_Symbol] :=
  (d+e*x^2)^p*(a+b*ArcSinh[c*x])/(2*p) - 
  b*c*d^p/(2*p)*Int[(1+c^2*x^2)^(p-1/2),x] + 
  d*Int[(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])/x,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])/x_,x_Symbol] :=
  (d+e*x^2)^p*(a+b*ArcCosh[c*x])/(2*p) - 
  b*c*(-d)^p/(2*p)*Int[(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2),x] + 
  d*Int[(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x])/x,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])/(f*(m+1)) - 
  b*c*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2),x] - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && IGtQ[p,0] && ILtQ[(m+1)/2,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])/(f*(m+1)) - 
  b*c*(-d)^p/(f*(m+1))*Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2),x] - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && ILtQ[(m+1)/2,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && IGtQ[p,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1+c^2*x^2)^p,x]},  
  Dist[d^p*(a+b*ArcSinh[c*x]),u,x] - b*c*d^p*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IntegerQ[p-1/2] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0]) && NeQ[p,-1/2] && GtQ[d,0]


Int[x_^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1+c*x)^p*(-1+c*x)^p,x]},  
  Dist[(-d1*d2)^p*(a+b*ArcCosh[c*x]),u,x] - b*c*(-d1*d2)^p*Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2] && 
  (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0]) && NeQ[p,-1/2] && GtQ[d1,0] && LtQ[d2,0]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1+c^2*x^2)^p,x]},
  (a+b*ArcSinh[c*x])*Int[x^m*(d+e*x^2)^p,x] - 
  b*c*d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p+1/2,0] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])


Int[x_^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1+c*x)^p*(-1+c*x)^p,x]},  
  (a+b*ArcCosh[c*x])*Int[x^m*(d1+e1*x)^p*(d2+e2*x)^p,x] - 
  b*c*(-d1*d2)^(p-1/2)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(Sqrt[1+c*x]*Sqrt[-1+c*x])*
    Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[p+1/2,0] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d)^p/(f*(m+1))*Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && IntegerQ[p]


(* Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(f*(m+1)) - 
  2*e1*e2*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^p/(f*(m+1))*Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && 
  IntegerQ[p-1/2] && (GtQ[d1,0] && LtQ[d2,0]) *)


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/(f*(m+1)) - 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+1)*Sqrt[1+c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1),x] - 
  c^2*Sqrt[d+e*x^2]/(f^2*(m+1)*Sqrt[1+c^2*x^2])*Int[(f*x)^(m+2)*(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/(f*(m+1)) - 
  b*c*n*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(f*(m+1)*Sqrt[1+c*x]*Sqrt[-1+c*x])*
    Int[(f*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1),x] - 
  c^2*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(f^2*(m+1)*Sqrt[1+c*x]*Sqrt[-1+c*x])*
    Int[((f*x)^(m+2)*(a+b*ArcCosh[c*x])^n)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(f*(m+1)) - 
  2*e1*e2*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^(p-1/2)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(f*(m+1)*Sqrt[1+c*x]*Sqrt[-1+c*x])*
    Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && IntegerQ[p-1/2]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+2*p+1))*Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]] && (IntegerQ[p] || GtQ[d,0]) && (RationalQ[m] || EqQ[n,1]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d)^p/(f*(m+2*p+1))*Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]] && IntegerQ[p] && (RationalQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/(f*(m+2)) - 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+2)*Sqrt[1+c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/((m+2)*Sqrt[1+c^2*x^2])*Int[(f*x)^m*(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[n,0] && Not[LtQ[m,-1]] && (RationalQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/(f*(m+2)) - 
  b*c*n*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(f*(m+2)*Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[(f*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1),x] - 
  Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/((m+2)*Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[(f*x)^m*(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && Not[LtQ[m,-1]] && (RationalQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+2*p+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]] && (RationalQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(f*(m+2*p+1)) + 
  2*d1*d2*p/(m+2*p+1)*Int[(f*x)^m*(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^(p-1/2)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(f*(m+2*p+1)*Sqrt[1+c*x]*Sqrt[-1+c*x])*
    Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]] && 
  IntegerQ[p-1/2] && (RationalQ[m] || EqQ[n,1])


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(d*f*(m+1)) - 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] + 
  b*c*n*(-d)^p/(f*(m+1))*Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m] && IntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(d*f*(m+1)) - 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d1*d2*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] + 
  b*c*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(f*(m+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m] && IntegerQ[p+1/2]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d1*d2*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] + 
  b*c*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(f*(m+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] - 
  b*f*n*d^p/(2*c*(p+1))*Int[(f*x)^(m-1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && GtQ[m,1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*f*n*(-d)^p/(2*c*(p+1))*Int[(f*x)^(m-1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] - 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && GtQ[m,1]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e1*e2*(p+1)) - 
  f^2*(m-1)/(2*e1*e2*(p+1))*Int[(f*x)^(m-2)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*f*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(2*c*(p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m-1)*(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[p+1/2]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e1*e2*(p+1)) - 
  f^2*(m-1)/(2*e1*e2*(p+1))*Int[(f*x)^(m-2)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*f*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(2*c*(p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m-1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && LtQ[p,-1] && Not[IntegerQ[p]] && GtQ[m,1]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] + 
  b*c*n*d^p/(2*f*(p+1))*Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[p] || GtQ[d,0]) && 
  (IntegerQ[m] || IntegerQ[p] || EqQ[n,1]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d)^p/(2*f*(p+1))*Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && IntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*f*(p+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[m] || IntegerQ[p] || EqQ[n,1])


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d1*d2*f*(p+1)) + 
  (m+2*p+3)/(2*d1*d2*(p+1))*Int[(f*x)^m*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(2*f*(p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && 
  (IntegerQ[m] || EqQ[n,1]) && IntegerQ[p+1/2]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d1*d2*f*(p+1)) + 
  (m+2*p+3)/(2*d1*d2*(p+1))*Int[(f*x)^m*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  b*c*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(2*f*(p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && 
  (IntegerQ[m] || IntegerQ[p] || EqQ[n,1])


(* Int[(f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/(e*m) - 
  b*f*n*Sqrt[1+c^2*x^2]/(c*m*Sqrt[d+e*x^2])*Int[(f*x)^(m-1)*(a+b*ArcSinh[c*x])^(n-1),x] - 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcSinh[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[m,1] && GtQ[d,0] && IntegerQ[m] *)


(* Int[(f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/(e1*e2*m) + 
  b*f*n*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(c*d1*d2*m*Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[(f*x)^(m-1)*(a+b*ArcCosh[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[(f*x)^(m-2)*(a+b*ArcCosh[c*x])^n/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && GtQ[m,1] && IntegerQ[m] *)


Int[(f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/(e*m) - 
  b*f*n*Sqrt[1+c^2*x^2]/(c*m*Sqrt[d+e*x^2])*Int[(f*x)^(m-1)*(a+b*ArcSinh[c*x])^(n-1),x] - 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcSinh[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[m,1] && IntegerQ[m]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/(e1*e2*m) + 
  b*f*n*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(c*d1*d2*m*Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[(f*x)^(m-1)*(a+b*ArcCosh[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[(f*x)^(m-2)*(a+b*ArcCosh[c*x])^n/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && GtQ[m,1] && IntegerQ[m]


Int[x_^m_*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*Sinh[x]^m,x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[d,0] && IGtQ[n,0] && IntegerQ[m]


Int[x_^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  1/(c^(m+1)*Sqrt[-d1*d2])*Subst[Int[(a+b*x)^n*Cosh[x]^m,x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[n,0] && GtQ[d1,0] && LtQ[d2,0] && IntegerQ[m]


Int[(f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*(a+b*ArcSinh[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,-c^2*x^2]/(Sqrt[d]*f*(m+1)) - 
  b*c*(f*x)^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},-c^2*x^2]/(Sqrt[d]*f^2*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[d,0] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*Sqrt[1-c^2*x^2]*(a+b*ArcCosh[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2]/
    (f*(m+1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]) + 
  b*c*(f*x)^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2]/(Sqrt[-d1*d2]*f^2*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[d1,0] && LtQ[d2,0] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(f*x)^m*(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[n,0] && Not[GtQ[d,0]] && (IntegerQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  Sqrt[1+c*x]*Sqrt[-1+c*x]/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x])*Int[(f*x)^m*(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && Not[GtQ[d1,0] && LtQ[d2,0]] && (IntegerQ[m] || EqQ[n,1])


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(e*(m+2*p+1)) - 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] - 
  b*f*n*d^p/(c*(m+2*p+1))*Int[(f*x)^(m-1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && (IntegerQ[p] || GtQ[d,0]) && IntegerQ[m] *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] - 
  b*f*n*(-d)^p/(c*(m+2*p+1))*Int[(f*x)^(m-1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[p] && IntegerQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(e*(m+2*p+1)) - 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] - 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(c*(m+2*p+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[m]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(e1*e2*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] - 
  b*f*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(c*(m+2*p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m-1)*(-1+c^2*x^2)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[m] && IntegerQ[p+1/2]


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(e1*e2*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] - 
  b*f*n*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(c*(m+2*p+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m-1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[m]


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  d^p*(f*x)^m*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[e,c^2*d] && LtQ[n,-1] && EqQ[m+2*p+1,0] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1+c*x]*Sqrt[-1+c*x]*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*(-d)^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && EqQ[m+2*p+1,0] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1+c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[e,c^2*d] && LtQ[n,-1] && EqQ[m+2*p+1,0]


Int[(f_.*x_)^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1+c*x]*Sqrt[-1+c*x]*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(b*c*(n+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m-1)*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && LtQ[n,-1] && EqQ[m+2*p+1,0] && IntegerQ[p-1/2]


Int[(f_.*x_)^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1+c*x]*Sqrt[-1+c*x]*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(b*c*(n+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m-1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m,p},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && LtQ[n,-1] && EqQ[m+2*p+1,0]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^m*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  f*m/(b*c*Sqrt[d]*(n+1))*Int[(f*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && LtQ[n,-1] && GtQ[d,0]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  (f*x)^m*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) - 
  (f*m)/(b*c*Sqrt[-d1*d2]*(n+1))*Int[(f*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && LtQ[n,-1] && GtQ[d1,0] && LtQ[d2,0]


(* Int[(f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(f*x)^m*(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && LtQ[n,-1] && Not[GtQ[d,0]] *)


(* Int[(f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  Sqrt[1+c*x]*Sqrt[-1+c*x]/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x])*Int[(f*x)^m*(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && LtQ[n,-1] && Not[GtQ[d1,0] && LtQ[d2,0]] *)


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  d^p*(f*x)^m*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] - 
  c*d^p*(m+2*p+1)/(b*f*(n+1))*Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && LtQ[n,-1] && IGtQ[m,-3] && IGtQ[2*p,0] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1+c*x]*Sqrt[-1+c*x]*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*(-d)^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] - 
  c*(-d)^p*(m+2*p+1)/(b*f*(n+1))*Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IGtQ[m,-3] && IGtQ[p,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1+c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] - 
  c*(m+2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*f*(n+1)*(1+c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && LtQ[n,-1] && IGtQ[m,-3] && IGtQ[2*p,0]


Int[(f_.*x_)^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1+c*x]*Sqrt[-1+c*x]*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(b*c*(n+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m-1)*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] - 
  c*(m+2*p+1)*(-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(b*f*(n+1)*(1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && LtQ[n,-1] && IGtQ[m,-3] && IGtQ[p+1/2,0]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Sinh[x]^m*Cosh[x]^(2*p+1),x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && IntegerQ[2*p] && GtQ[p,-1] && IGtQ[m,0] && (IntegerQ[p] || GtQ[d,0])


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d)^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cosh[x]^m*Sinh[x]^(2*p+1),x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && IGtQ[m,0]


Int[x_^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d1*d2)^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cosh[x]^m*Sinh[x]^(2*p+1),x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p+1/2] && GtQ[p,-1] && IGtQ[m,0] && (GtQ[d1,0] && LtQ[d2,0])


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1+c^2*x^2)^FracPart[p]*Int[x^m*(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && IntegerQ[2*p] && GtQ[p,-1] && IGtQ[m,0] && Not[(IntegerQ[p] || GtQ[d,0])]


Int[x_^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/((1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[x^m*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[2*p] && GtQ[p,-1] && IGtQ[m,0] && 
  Not[IntegerQ[p] || GtQ[d1,0] && LtQ[d2,0]]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[e,c^2*d] && GtQ[d,0] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] && (EqQ[m,-1] || EqQ[m,-2])


Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]),(f*x)^m*(d1+e1*x)^(p+1/2)*(d2+e2*x)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] && 
  (EqQ[m,-1] || EqQ[m,-2])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  d*(f*x)^(m+1)*(a+b*ArcCosh[c*x])/(f*(m+1)) + 
  e*(f*x)^(m+3)*(a+b*ArcCosh[c*x])/(f^3*(m+3)) - 
  b*c/(f*(m+1)*(m+3))*Int[(f*x)^(m+1)*(d*(m+3)+e*(m+1)*x^2)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e,0] && NeQ[m,-1] && NeQ[m,-3]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])/(2*e*(p+1)) - b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[e,c^2*d] && NeQ[p,-1]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])/(2*e*(p+1)) - b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[c^2*d+e,0] && NeQ[p,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[e,c^2*d] && IntegerQ[p] && (GtQ[p,0] || IGtQ[(m-1)/2,0] && LeQ[m+p,0])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[(m-1)/2,0] && LeQ[m+p,0])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[e,c^2*d] && IGtQ[n,0] && IntegerQ[p] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[c^2*d+e,0] && IGtQ[n,0] && IntegerQ[p] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,m,n,p},x]


Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^FracPart[p]*(f+g*x)^FracPart[p]/(d*f+e*g*x^2)^FracPart[p]*
    Int[(h*x)^m*(d*f+e*g*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[e*f+d*g,0] && EqQ[c^2*f^2+g^2,0] && Not[IntegerQ[p]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d)^IntPart[p]*(d+e*x^2)^FracPart[p]/((1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f*x)^m*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[c^2*d+e,0] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*7.1.5 u (a+b arcsinh(c x))^n*)


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_.+e_.*x_),x_Symbol] :=
  Subst[Int[(a+b*x)^n*Cosh[x]/(c*d+e*Sinh[x]),x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[n,0]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(d_.+e_.*x_),x_Symbol] :=
  Subst[Int[(a+b*x)^n*Sinh[x]/(c*d+e*Cosh[x]),x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[n,0]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcSinh[c*x])^n/(e*(m+1)) - 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,0] && NeQ[m,-1]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCosh[c*x])^n/(e*(m+1)) - 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,0] && NeQ[m,-1]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[m,0] && LtQ[n,-1]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[m,0] && LtQ[n,-1]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Cosh[x]*(c*d+e*Sinh[x])^m,x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[m,0]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*(c*d+e*Cosh[x])^m*Sinh[x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[m,0]


Int[Px_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[ExpandExpression[Px,x],x]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x]


Int[Px_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[ExpandExpression[Px,x],x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Sqrt[1-c^2*x^2]/(Sqrt[-1+c*x]*Sqrt[1+c*x])*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x]


(* Int[Px_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  With[{u=IntHide[Px,x]},  
  Dist[(a+b*ArcSinh[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x] && IGtQ[n,0] *)


(* Int[Px_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  With[{u=IntHide[Px,x]},  
  Dist[(a+b*ArcCosh[c*x])^n,u,x] - 
    b*c*n*Sqrt[1-c^2*x^2]/(Sqrt[-1+c*x]*Sqrt[1+c*x])*Int[SimplifyIntegrand[u*(a+b*ArcCosh[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x] && IGtQ[n,0] *)


Int[Px_*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]


Int[Px_*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]


Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[Px*(d+e*x)^m,x]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]


Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[Px*(d+e*x)^m,x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Sqrt[1-c^2*x^2]/(Sqrt[-1+c*x]*Sqrt[1+c*x])*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]


Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},  
  Dist[(a+b*ArcSinh[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[m,0] && LtQ[m+p+1,0]


Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},  
  Dist[(a+b*ArcCosh[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[m,0] && LtQ[m+p+1,0]


Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
  With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},  
  Dist[(a+b*ArcSinh[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[n,0] && IGtQ[p,0] && EqQ[e*g-2*d*h,0]


Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
  With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},  
  Dist[(a+b*ArcCosh[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[n,0] && IGtQ[p,0] && EqQ[e*g-2*d*h,0]


Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && IGtQ[n,0] && IntegerQ[m]


Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && IGtQ[n,0] && IntegerQ[m]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f+g*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[Dist[1/Sqrt[1+c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IGtQ[m,0] && ILtQ[p+1/2,0] && GtQ[d,0] && (LtQ[m,-2*p-1] || GtQ[m,3])


Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f+g*x)^m*(d1+e1*x)^p*(d2+e2*x)^p,x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[Dist[1/(Sqrt[1+c*x]*Sqrt[-1+c*x]),u,x],x]] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[m,0] && ILtQ[p+1/2,0] && GtQ[d1,0] && LtQ[d2,0] && 
  (LtQ[m,-2*p-1] || GtQ[m,3])


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IGtQ[m,0] && IntegerQ[p+1/2] && GtQ[d,0] && IGtQ[n,0] && 
  (EqQ[n,1] && GtQ[p,-1] || GtQ[p,0] || EqQ[m,1] || EqQ[m,2] && LtQ[p,-2])


Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[m,0] && IntegerQ[p+1/2] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0] && 
  (EqQ[n,1] && GtQ[p,-1] || GtQ[p,0] || EqQ[m,1] || EqQ[m,2] && LtQ[p,-2])


Int[(f_.+g_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f+g*x)^m*(d+e*x^2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  1/(b*c*Sqrt[d]*(n+1))*Int[(d*g*m+2*e*f*x+e*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && ILtQ[m,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_*Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f+g*x)^m*(d1*d2+e1*e2*x^2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) - 
  1/(b*c*Sqrt[-d1*d2]*(n+1))*Int[(d1*d2*g*m+2*e1*e2*f*x+e1*e2*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && ILtQ[m,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n,(f+g*x)^m*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IntegerQ[m] && IGtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n,(f+g*x)^m*(d1+e1*x)^(p-1/2)*(d2+e2*x)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[m] && IGtQ[p+1/2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (f+g*x)^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  1/(b*c*Sqrt[d]*(n+1))*
    Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),(d*g*m+e*f*(2*p+1)*x+e*g*(m+2*p+1)*x^2)*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && ILtQ[m,0] && IGtQ[p-1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (f+g*x)^m*(d1+e1*x)^(p+1/2)*(d2+e2*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) - 
  1/(b*c*Sqrt[-d1*d2]*(n+1))*
    Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),
      (d1*d2*g*m+e1*e2*f*(2*p+1)*x+e1*e2*g*(m+2*p+1)*x^2)*(d1+e1*x)^(p-1/2)*(d2+e2*x)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && ILtQ[m,0] && IGtQ[p-1/2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f+g*x)^m*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IGtQ[m,0] && GtQ[d,0] && LtQ[n,-1]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  (f+g*x)^m*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) - 
  g*m/(b*c*Sqrt[-d1*d2]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[m,0] && GtQ[d1,0] && LtQ[d2,0] && LtQ[n,-1]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*(c*f+g*Sinh[x])^m,x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e,c^2*d] && IntegerQ[m] && GtQ[d,0] && (GtQ[m,0] || IGtQ[n,0])


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  1/(c^(m+1)*Sqrt[-d1*d2])*Subst[Int[(a+b*x)^n*(c*f+g*Cosh[x])^m,x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[m] && GtQ[d1,0] && LtQ[d2,0] && (GtQ[m,0] || IGtQ[n,0])


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n/Sqrt[d+e*x^2],(f+g*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IntegerQ[m] && ILtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]),(f+g*x)^m*(d1+e1*x)^(p+1/2)*(d2+e2*x)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[m] && ILtQ[p+1/2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1+c^2*x^2)^FracPart[p]*Int[(f+g*x)^m*(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e,c^2*d] && IntegerQ[m] && IntegerQ[p-1/2] && Not[GtQ[d,0]]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d)^IntPart[p]*(d+e*x^2)^FracPart[p]/((1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[(f+g*x)^m*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p-1/2]


Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*
    Int[(f+g*x)^m*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[m] && IntegerQ[p-1/2] && Not[GtQ[d1,0] && LtQ[d2,0]]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Log[h*(f+g*x)^m]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(a+b*ArcSinh[c*x])^(n+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && EqQ[e,c^2*d] && GtQ[d,0] && IGtQ[n,0]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  Log[h*(f+g*x)^m]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) - 
  g*m/(b*c*Sqrt[-d1*d2]*(n+1))*Int[(a+b*ArcCosh[c*x])^(n+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g,h,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1+c^2*x^2)^FracPart[p]*Int[Log[h*(f+g*x)^m]*(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e,c^2*d] && IntegerQ[p-1/2] && Not[GtQ[d,0]]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d)^IntPart[p]*(d+e*x^2)^FracPart[p]/((1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[Log[h*(f+g*x)^m]*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/((1+c*x)^FracPart[p]*(-1+c*x)^FracPart[p])*
    Int[Log[h*(f+g*x)^m]*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g,h,m,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2] && Not[GtQ[d1,0] && LtQ[d2,0]]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[Dist[1/Sqrt[1+c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m+1/2,0]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[Dist[1/(Sqrt[1+c*x]*Sqrt[-1+c*x]),u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m+1/2,0]


Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n,(d+e*x)^m*(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]


Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n,(d+e*x)^m*(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]


Int[u_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[a+b*ArcSinh[c*x],v,x] - b*c*Int[SimplifyIntegrand[v/Sqrt[1+c^2*x^2],x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[u_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[a+b*ArcCosh[c*x],v,x] - b*c*Sqrt[1-c^2*x^2]/(Sqrt[-1+c*x]*Sqrt[1+c*x])*Int[SimplifyIntegrand[v/Sqrt[1-c^2*x^2],x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[Px_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n},x] && PolynomialQ[Px,x] && EqQ[e,c^2*d] && IntegerQ[p-1/2]


Int[Px_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && PolynomialQ[Px,x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2]


Int[Px_.*(f_+g_.*(d_+e_.*x_^2)^p_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(f+g*(d+e*x^2)^p)^m*(a+b*ArcSinh[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PolynomialQ[Px,x] && EqQ[e,c^2*d] && IGtQ[p+1/2,0] && IntegersQ[m,n]


Int[Px_.*(f_+g_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(f+g*(d1+e1*x)^p*(d2+e2*x)^p)^m*(a+b*ArcCosh[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && PolynomialQ[Px,x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[p+1/2,0] && IntegersQ[m,n]


Int[RFx_*ArcSinh[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[ArcSinh[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[c,x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[RFx_*ArcCosh[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[ArcCosh[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[c,x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[RFx_*(a_+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[RFx*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[RFx_*(a_+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[RFx*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[RFx_*(d_+e_.*x_^2)^p_*ArcSinh[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(d+e*x^2)^p*ArcSinh[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[e,c^2*d] && IntegerQ[p-1/2]


Int[RFx_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*ArcCosh[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(d1+e1*x)^p*(d2+e2*x)^p*ArcCosh[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{c,d1,e1,d2,e2},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2]


Int[RFx_*(d_+e_.*x_^2)^p_*(a_+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p,RFx*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[e,c^2*d] && IntegerQ[p-1/2]


Int[RFx_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d1+e1*x)^p*(d2+e2*x)^p,RFx*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d1,e1,d2,e2},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2]


Int[u_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*7.1.6 Miscellaneous inverse hyperbolic sine*)
(**)


Int[(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x]


Int[(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^p*(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^p*(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[Sqrt[a_.+b_.*ArcSinh[c_+d_.*x_^2]],x_Symbol] :=
  x*Sqrt[a+b*ArcSinh[c+d*x^2]] - 
  Sqrt[Pi]*x*(Cosh[a/(2*b)]-c*Sinh[a/(2*b)])*FresnelC[Sqrt[-c/(Pi*b)]*Sqrt[a+b*ArcSinh[c+d*x^2]]]/
    (Sqrt[-(c/b)]*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) + 
  Sqrt[Pi]*x*(Cosh[a/(2*b)]+c*Sinh[a/(2*b)])*FresnelS[Sqrt[-c/(Pi*b)]*Sqrt[a+b*ArcSinh[c+d*x^2]]]/
    (Sqrt[-(c/b)]*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]


Int[(a_.+b_.*ArcSinh[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcSinh[c+d*x^2])^n - 
  2*b*n*Sqrt[2*c*d*x^2+d^2*x^4]*(a+b*ArcSinh[c+d*x^2])^(n-1)/(d*x) + 
  4*b^2*n*(n-1)*Int[(a+b*ArcSinh[c+d*x^2])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,-1] && GtQ[n,1]


Int[1/(a_.+b_.*ArcSinh[c_+d_.*x_^2]),x_Symbol] :=
  x*(c*Cosh[a/(2*b)]-Sinh[a/(2*b)])*CoshIntegral[(a+b*ArcSinh[c+d*x^2])/(2*b)]/
    (2*b*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[(1/2)*ArcSinh[c+d*x^2]])) + 
  x*(Cosh[a/(2*b)]-c*Sinh[a/(2*b)])*SinhIntegral[(a+b*ArcSinh[c+d*x^2])/(2*b)]/
    (2*b*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[(1/2)*ArcSinh[c+d*x^2]])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]


Int[1/Sqrt[a_.+b_.*ArcSinh[c_+d_.*x_^2]],x_Symbol] :=
  (c+1)*Sqrt[Pi/2]*x*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Erfi[Sqrt[a+b*ArcSinh[c+d*x^2]]/Sqrt[2*b]]/
    (2*Sqrt[b]*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) + 
  (c-1)*Sqrt[Pi/2]*x*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Erf[Sqrt[a+b*ArcSinh[c+d*x^2]]/Sqrt[2*b]]/
    (2*Sqrt[b]*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]


Int[1/(a_.+b_.*ArcSinh[c_+d_.*x_^2])^(3/2),x_Symbol] :=
  -Sqrt[2*c*d*x^2+d^2*x^4]/(b*d*x*Sqrt[a+b*ArcSinh[c+d*x^2]]) - 
  (-c/b)^(3/2)*Sqrt[Pi]*x*(Cosh[a/(2*b)]-c*Sinh[a/(2*b)])*FresnelC[Sqrt[-c/(Pi*b)]*Sqrt[a+b*ArcSinh[c+d*x^2]]]/
    (Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2]) + 
  (-c/b)^(3/2)*Sqrt[Pi]*x*(Cosh[a/(2*b)]+c*Sinh[a/(2*b)])*FresnelS[Sqrt[-c/(Pi*b)]*Sqrt[a+b*ArcSinh[c+d*x^2]]]/
    (Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2]) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]


Int[1/(a_.+b_.*ArcSinh[c_+d_.*x_^2])^2,x_Symbol] :=
  -Sqrt[2*c*d*x^2+d^2*x^4]/(2*b*d*x*(a+b*ArcSinh[c+d*x^2])) + 
  x*(Cosh[a/(2*b)]-c*Sinh[a/(2*b)])*CoshIntegral[(a+b*ArcSinh[c+d*x^2])/(2*b)]/
    (4*b^2*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) + 
  x*(c*Cosh[a/(2*b)]-Sinh[a/(2*b)])*SinhIntegral[(a+b*ArcSinh[c+d*x^2])/(2*b)]/
    (4*b^2*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]


Int[(a_.+b_.*ArcSinh[c_+d_.*x_^2])^n_,x_Symbol] :=
  -x*(a+b*ArcSinh[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) + 
  Sqrt[2*c*d*x^2+d^2*x^4]*(a+b*ArcSinh[c+d*x^2])^(n+1)/(2*b*d*(n+1)*x) + 
  1/(4*b^2*(n+1)*(n+2))*Int[(a+b*ArcSinh[c+d*x^2])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,-1] && LtQ[n,-1] && NeQ[n,-2]


Int[Sqrt[a_.+b_.*ArcCosh[1+d_.*x_^2]],x_Symbol] :=
  2*Sqrt[a+b*ArcCosh[1+d*x^2]]*Sinh[(1/2)*ArcCosh[1+d*x^2]]^2/(d*x) - 
  Sqrt[b]*Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Sinh[(1/2)*ArcCosh[1+d*x^2]]*
    Erfi[(1/Sqrt[2*b])*Sqrt[a+b*ArcCosh[1+d*x^2]]]/(d*x) + 
  Sqrt[b]*Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Sinh[(1/2)*ArcCosh[1+d*x^2]]*
    Erf[(1/Sqrt[2*b])*Sqrt[a+b*ArcCosh[1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[Sqrt[a_.+b_.*ArcCosh[-1+d_.*x_^2]],x_Symbol] :=
  2*Sqrt[a+b*ArcCosh[-1+d*x^2]]*Cosh[(1/2)*ArcCosh[-1+d*x^2]]^2/(d*x) - 
  Sqrt[b]*Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Cosh[(1/2)*ArcCosh[-1+d*x^2]]*
    Erfi[(1/Sqrt[2*b])*Sqrt[a+b*ArcCosh[-1+d*x^2]]]/(d*x) - 
  Sqrt[b]*Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Cosh[(1/2)*ArcCosh[-1+d*x^2]]*
    Erf[(1/Sqrt[2*b])*Sqrt[a+b*ArcCosh[-1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[(a_.+b_.*ArcCosh[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcCosh[c+d*x^2])^n - 
  2*b*n*(2*c*d*x^2+d^2*x^4)*(a+b*ArcCosh[c+d*x^2])^(n-1)/(d*x*Sqrt[-1+c+d*x^2]*Sqrt[1+c+d*x^2]) + 
  4*b^2*n*(n-1)*Int[(a+b*ArcCosh[c+d*x^2])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && GtQ[n,1]


Int[1/(a_.+b_.*ArcCosh[1+d_.*x_^2]),x_Symbol] :=
  x*Cosh[a/(2*b)]*CoshIntegral[(a+b*ArcCosh[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) - 
  x*Sinh[a/(2*b)]*SinhIntegral[(a+b*ArcCosh[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCosh[-1+d_.*x_^2]),x_Symbol] :=
  -x*Sinh[a/(2*b)]*CoshIntegral[(a+b*ArcCosh[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) + 
  x*Cosh[a/(2*b)]*SinhIntegral[(a+b*ArcCosh[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/Sqrt[a_.+b_.*ArcCosh[1+d_.*x_^2]],x_Symbol] :=
  Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Sinh[ArcCosh[1+d*x^2]/2]*Erfi[Sqrt[a+b*ArcCosh[1+d*x^2]]/Sqrt[2*b]]/(Sqrt[b]*d*x) + 
  Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Sinh[ArcCosh[1+d*x^2]/2]*Erf[Sqrt[a+b*ArcCosh[1+d*x^2]]/Sqrt[2*b]]/(Sqrt[b]*d*x) /;
FreeQ[{a,b,d},x]


Int[1/Sqrt[a_.+b_.*ArcCosh[-1+d_.*x_^2]],x_Symbol] :=
  Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Cosh[ArcCosh[-1+d*x^2]/2]*Erfi[Sqrt[a+b*ArcCosh[-1+d*x^2]]/Sqrt[2*b]]/(Sqrt[b]*d*x) - 
  Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Cosh[ArcCosh[-1+d*x^2]/2]*Erf[Sqrt[a+b*ArcCosh[-1+d*x^2]]/Sqrt[2*b]]/(Sqrt[b]*d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCosh[1+d_.*x_^2])^(3/2),x_Symbol] :=
  -Sqrt[d*x^2]*Sqrt[2+d*x^2]/(b*d*x*Sqrt[a+b*ArcCosh[1+d*x^2]]) + 
  Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Sinh[ArcCosh[1+d*x^2]/2]*Erfi[Sqrt[a+b*ArcCosh[1+d*x^2]]/Sqrt[2*b]]/(b^(3/2)*d*x)- 
  Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Sinh[ArcCosh[1+d*x^2]/2]*Erf[Sqrt[a+b*ArcCosh[1+d*x^2]]/Sqrt[2*b]]/(b^(3/2)*d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCosh[-1+d_.*x_^2])^(3/2),x_Symbol] :=
  -Sqrt[d*x^2]*Sqrt[-2+d*x^2]/(b*d*x*Sqrt[a+b*ArcCosh[-1+d*x^2]]) + 
  Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Cosh[ArcCosh[-1+d*x^2]/2]*Erfi[Sqrt[a+b*ArcCosh[-1+d*x^2]]/Sqrt[2*b]]/(b^(3/2)*d*x) + 
  Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Cosh[ArcCosh[-1+d*x^2]/2]*Erf[Sqrt[a+b*ArcCosh[-1+d*x^2]]/Sqrt[2*b]]/(b^(3/2)*d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCosh[1+d_.*x_^2])^2,x_Symbol] :=
  -Sqrt[d*x^2]*Sqrt[2+d*x^2]/(2*b*d*x*(a+b*ArcCosh[1+d*x^2])) - 
  x*Sinh[a/(2*b)]*CoshIntegral[(a+b*ArcCosh[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) + 
  x*Cosh[a/(2*b)]*SinhIntegral[(a+b*ArcCosh[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCosh[-1+d_.*x_^2])^2,x_Symbol] :=
  -Sqrt[d*x^2]*Sqrt[-2+d*x^2]/(2*b*d*x*(a+b*ArcCosh[-1+d*x^2])) + 
  x*Cosh[a/(2*b)]*CoshIntegral[(a+b*ArcCosh[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) - 
  x*Sinh[a/(2*b)]*SinhIntegral[(a+b*ArcCosh[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) /;
FreeQ[{a,b,d},x]


Int[(a_.+b_.*ArcCosh[c_+d_.*x_^2])^n_,x_Symbol] :=
  -x*(a+b*ArcCosh[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) + 
  (2*c*x^2 +d*x^4)*(a+b*ArcCosh[c+d*x^2])^(n+1)/(2*b*(n+1)*x*Sqrt[-1+c+d*x^2]*Sqrt[1+c+d*x^2]) + 
  1/(4*b^2*(n+1)*(n+2))*Int[(a+b*ArcCosh[c+d*x^2])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && LtQ[n,-1] && NeQ[n,-2]


Int[ArcSinh[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Coth[x],x],x,ArcSinh[a*x^p]] /;
FreeQ[{a,p},x] && IGtQ[n,0]


Int[ArcCosh[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Tanh[x],x],x,ArcCosh[a*x^p]] /;
FreeQ[{a,p},x] && IGtQ[n,0]


Int[u_.*ArcSinh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCsch[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCosh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSech[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[ArcSinh[Sqrt[-1+b_.*x_^2]]^n_./Sqrt[-1+b_.*x_^2],x_Symbol] :=
  Sqrt[b*x^2]/(b*x)*Subst[Int[ArcSinh[x]^n/Sqrt[1+x^2],x],x,Sqrt[-1+b*x^2]] /;
FreeQ[{b,n},x]


Int[ArcCosh[Sqrt[1+b_.*x_^2]]^n_./Sqrt[1+b_.*x_^2],x_Symbol] :=
  Sqrt[-1+Sqrt[1+b*x^2]]*Sqrt[1+Sqrt[1+b*x^2]]/(b*x)*Subst[Int[ArcCosh[x]^n/(Sqrt[-1+x]*Sqrt[1+x]),x],x,Sqrt[1+b*x^2]] /;
FreeQ[{b,n},x]


Int[f_^(c_.*ArcSinh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[f^(c*x^n)*Cosh[x],x],x,ArcSinh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && IGtQ[n,0]


Int[f_^(c_.*ArcCosh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[f^(c*x^n)*Sinh[x],x],x,ArcCosh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && IGtQ[n,0]


Int[x_^m_.*f_^(c_.*ArcSinh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[(-a/b+Sinh[x]/b)^m*f^(c*x^n)*Cosh[x],x],x,ArcSinh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[x_^m_.*f_^(c_.*ArcCosh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[(-a/b+Cosh[x]/b)^m*f^(c*x^n)*Sinh[x],x],x,ArcCosh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[ArcSinh[u_],x_Symbol] :=
  x*ArcSinh[u] -
  Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1+u^2],x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCosh[u_],x_Symbol] :=
  x*ArcCosh[u] - 
  Int[SimplifyIntegrand[x*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSinh[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcSinh[u])/(d*(m+1)) -
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1+u^2],x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCosh[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCosh[u])/(d*(m+1)) -
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSinh[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcSinh[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1+u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCosh[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCosh[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


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





(* ::Subsection::Closed:: *)
(*7.2.1 u (a+b arctanh(c x^n))^p*)


Int[(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
  x*(a+b*ArcTanh[c*x^n])^p - 
  b*c*n*p*Int[x^n*(a+b*ArcTanh[c*x^n])^(p-1)/(1-c^2*x^(2*n)),x] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0] && (EqQ[p,1] || EqQ[n,1])


Int[(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
  x*(a+b*ArcCoth[c*x^n])^p - 
  b*c*n*p*Int[x^n*(a+b*ArcCoth[c*x^n])^(p-1)/(1-c^2*x^(2*n)),x] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0] && (EqQ[p,1] || EqQ[n,1])


Int[(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*Log[1+c*x^n]/2-b*Log[1-c*x^n]/2)^p,x],x] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0] && IntegerQ[n]


Int[(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*Log[1+x^(-n)/c]/2-b*Log[1-x^(-n)/c]/2)^p,x],x] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0] && IntegerQ[n]


Int[(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(a+b*ArcTanh[c*x^n])^p,x] /;
FreeQ[{a,b,c,n,p},x]


Int[(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(a+b*ArcCoth[c*x^n])^p,x] /;
FreeQ[{a,b,c,n,p},x]


Int[(a_.+b_.*ArcTanh[c_.*x_])/x_,x_Symbol] :=
  a*Log[x] - b/2*PolyLog[2,-c*x] + b/2*PolyLog[2,c*x] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcCoth[c_.*x_])/x_,x_Symbol] :=
  a*Log[x] + b/2*PolyLog[2,-1/(c*x)] - b/2*PolyLog[2,1/(c*x)] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_/x_,x_Symbol] :=
  2*(a+b*ArcTanh[c*x])^p*ArcTanh[1-2/(1-c*x)] -
  2*b*c*p*Int[(a+b*ArcTanh[c*x])^(p-1)*ArcTanh[1-2/(1-c*x)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IGtQ[p,1]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_/x_,x_Symbol] :=
  2*(a+b*ArcCoth[c*x])^p*ArcCoth[1-2/(1-c*x)] -
  2*b*c*p*Int[(a+b*ArcCoth[c*x])^(p-1)*ArcCoth[1-2/(1-c*x)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IGtQ[p,1]


Int[(a_.+b_.*ArcTanh[c_.*x_^n_])^p_./x_,x_Symbol] :=
  1/n*Subst[Int[(a+b*ArcTanh[c*x])^p/x,x],x,x^n] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcCoth[c_.*x_^n_])^p_./x_,x_Symbol] :=
  1/n*Subst[Int[(a+b*ArcCoth[c*x])^p/x,x],x,x^n] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcTanh[c*x])^p/(d*(m+1)) - 
  b*c*p/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcTanh[c*x])^(p-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[p,0] && (EqQ[p,1] || IntegerQ[m]) && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCoth[c*x])^p/(d*(m+1)) - 
  b*c*p/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcCoth[c*x])^(p-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[p,0] && (EqQ[p,1] || IntegerQ[m]) && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_.]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcTanh[c*x^n])/(d*(m+1)) - 
  b*c*n/(d*(m+1))*Int[x^(n-1)*(d*x)^(m+1)/(1-c^2*x^(2*n)),x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_.]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCoth[c*x^n])/(d*(m+1)) - 
  b*c*n/(d*(m+1))*Int[x^(n-1)*(d*x)^(m+1)/(1-c^2*x^(2*n)),x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*(a+b*Log[1+c*x^n]/2-b*Log[1-c*x^n]/2)^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0] && IntegerQ[m] && IntegerQ[n]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*(a+b*Log[1+x^(-n)/c]/2-b*Log[1-x^(-n)/c]/2)^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0] && IntegerQ[m] && IntegerQ[n]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTanh[c*x])^p*Log[2/(1+e*x/d)]/e + 
  b*c*p/e*Int[(a+b*ArcTanh[c*x])^(p-1)*Log[2/(1+e*x/d)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCoth[c*x])^p*Log[2/(1+e*x/d)]/e + 
  b*c*p/e*Int[(a+b*ArcCoth[c*x])^(p-1)*Log[2/(1+e*x/d)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTanh[c*x])*Log[2/(1+c*x)]/e + 
  b*c/e*Int[Log[2/(1+c*x)]/(1-c^2*x^2),x] + 
  (a+b*ArcTanh[c*x])*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e - 
  b*c/e*Int[Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCoth[c*x])*Log[2/(1+c*x)]/e + 
  b*c/e*Int[Log[2/(1+c*x)]/(1-c^2*x^2),x] + 
  (a+b*ArcCoth[c*x])*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e - 
  b*c/e*Int[Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^2/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTanh[c*x])^2*Log[2/(1+c*x)]/e + 
  b*(a+b*ArcTanh[c*x])*PolyLog[2,1-2/(1+c*x)]/e + 
  b^2*PolyLog[3,1-2/(1+c*x)]/(2*e) + 
  (a+b*ArcTanh[c*x])^2*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e - 
  b*(a+b*ArcTanh[c*x])*PolyLog[2,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e - 
  b^2*PolyLog[3,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^2/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCoth[c*x])^2*Log[2/(1+c*x)]/e + 
  b*(a+b*ArcCoth[c*x])*PolyLog[2,1-2/(1+c*x)]/e + 
  b^2*PolyLog[3,1-2/(1+c*x)]/(2*e) + 
  (a+b*ArcCoth[c*x])^2*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e - 
  b*(a+b*ArcCoth[c*x])*PolyLog[2,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e - 
  b^2*PolyLog[3,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^3/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTanh[c*x])^3*Log[2/(1+c*x)]/e + 
  3*b*(a+b*ArcTanh[c*x])^2*PolyLog[2,1-2/(1+c*x)]/(2*e) + 
  3*b^2*(a+b*ArcTanh[c*x])*PolyLog[3,1-2/(1+c*x)]/(2*e) + 
  3*b^3*PolyLog[4,1-2/(1+c*x)]/(4*e) + 
  (a+b*ArcTanh[c*x])^3*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e - 
  3*b*(a+b*ArcTanh[c*x])^2*PolyLog[2,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) - 
  3*b^2*(a+b*ArcTanh[c*x])*PolyLog[3,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) - 
  3*b^3*PolyLog[4,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(4*e) /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^3/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCoth[c*x])^3*Log[2/(1+c*x)]/e + 
  3*b*(a+b*ArcCoth[c*x])^2*PolyLog[2,1-2/(1+c*x)]/(2*e) + 
  3*b^2*(a+b*ArcCoth[c*x])*PolyLog[3,1-2/(1+c*x)]/(2*e) + 
  3*b^3*PolyLog[4,1-2/(1+c*x)]/(4*e) + 
  (a+b*ArcCoth[c*x])^3*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e - 
  3*b*(a+b*ArcCoth[c*x])^2*PolyLog[2,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) - 
  3*b^2*(a+b*ArcCoth[c*x])*PolyLog[3,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) - 
  3*b^3*PolyLog[4,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(4*e) /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcTanh[c*x])/(e*(q+1)) - 
  b*c/(e*(q+1))*Int[(d+e*x)^(q+1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcCoth[c*x])/(e*(q+1)) - 
  b*c/(e*(q+1))*Int[(d+e*x)^(q+1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_,x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcTanh[c*x])^p/(e*(q+1)) - 
  b*c*p/(e*(q+1))*Int[ExpandIntegrand[(a+b*ArcTanh[c*x])^(p-1),(d+e*x)^(q+1)/(1-c^2*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,1] && IntegerQ[q] && NeQ[q,-1]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_,x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcCoth[c*x])^p/(e*(q+1)) - 
  b*c*p/(e*(q+1))*Int[ExpandIntegrand[(a+b*ArcCoth[c*x])^(p-1),(d+e*x)^(q+1)/(1-c^2*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,1] && IntegerQ[q] && NeQ[q,-1]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*Sqrt[x_]])^p_.,x_Symbol] :=
  2*Subst[Int[x*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p,x],x,Sqrt[x]] /;
FreeQ[{a,b,c,d,e,p,q},x]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*Sqrt[x_]])^p_.,x_Symbol] :=
  2*Subst[Int[x*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p,x],x,Sqrt[x]] /;
FreeQ[{a,b,c,d,e,p,q},x]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_^n_.]),x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcTanh[c*x^n])/(e*(q+1)) - 
  b*c*n/(e*(q+1))*Int[x^(n-1)*(d+e*x)^(q+1)/(1-c^2*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,q,n},x] && NeQ[q,-1]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_^n_.]),x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcCoth[c*x^n])/(e*(q+1)) - 
  b*c*n/(e*(q+1))*Int[x^(n-1)*(d+e*x)^(q+1)/(1-c^2*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,q,n},x] && NeQ[q,-1]


Int[(d_.+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(d+e*x)^q*(a+b*ArcTanh[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,q,n,p},x]


Int[(d_.+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(d+e*x)^q*(a+b*ArcCoth[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,q,n,p},x]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  f/e*Int[(f*x)^(m-1)*(a+b*ArcTanh[c*x])^p,x] - 
  d*f/e*Int[(f*x)^(m-1)*(a+b*ArcTanh[c*x])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0] && GtQ[m,0]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  f/e*Int[(f*x)^(m-1)*(a+b*ArcCoth[c*x])^p,x] - 
  d*f/e*Int[(f*x)^(m-1)*(a+b*ArcCoth[c*x])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0] && GtQ[m,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcTanh[c*x])^p*Log[2-2/(1+e*x/d)]/d - 
  b*c*p/d*Int[(a+b*ArcTanh[c*x])^(p-1)*Log[2-2/(1+e*x/d)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcCoth[c*x])^p*Log[2-2/(1+e*x/d)]/d - 
  b*c*p/d*Int[(a+b*ArcCoth[c*x])^(p-1)*Log[2-2/(1+e*x/d)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[(f*x)^m*(a+b*ArcTanh[c*x])^p,x] - 
  e/(d*f)*Int[(f*x)^(m+1)*(a+b*ArcTanh[c*x])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[(f*x)^m*(a+b*ArcCoth[c*x])^p,x] - 
  e/(d*f)*Int[(f*x)^(m+1)*(a+b*ArcCoth[c*x])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0] && LtQ[m,-1]


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcTanh[c*x]),u] - b*c*Int[SimplifyIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,q},x] && NeQ[q,-1] && IntegerQ[2*m] && (IGtQ[m,0] && IGtQ[q,0] || ILtQ[m+q+1,0] && LtQ[m*q,0])


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcCoth[c*x]),u] - b*c*Int[SimplifyIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,q},x] && NeQ[q,-1] && IntegerQ[2*m] && (IGtQ[m,0] && IGtQ[q,0] || ILtQ[m+q+1,0] && LtQ[m*q,0])


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_,x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcTanh[c*x])^p,u] - b*c*p*Int[ExpandIntegrand[(a+b*ArcTanh[c*x])^(p-1),u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,q},x] && IGtQ[p,1] && EqQ[c^2*d^2-e^2,0] && IntegersQ[m,q] && NeQ[m,-1] && NeQ[q,-1] && ILtQ[m+q+1,0] && LtQ[m*q,0]


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_,x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcCoth[c*x])^p,u] - b*c*p*Int[ExpandIntegrand[(a+b*ArcCoth[c*x])^(p-1),u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,q},x] && IGtQ[p,1] && EqQ[c^2*d^2-e^2,0] && IntegersQ[m,q] && NeQ[m,-1] && NeQ[q,-1] && ILtQ[m+q+1,0] && LtQ[m*q,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTanh[c*x])^p,(f*x)^m*(d+e*x)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0] && IntegerQ[q] && (GtQ[q,0] || NeQ[a,0] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCoth[c*x])^p,(f*x)^m*(d+e*x)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0] && IntegerQ[q] && (GtQ[q,0] || NeQ[a,0] || IntegerQ[m])


Int[x_^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*Sqrt[x_]])^p_.,x_Symbol] :=
  2*Subst[Int[x^(2*m+1)*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p,x],x,Sqrt[x]] /;
FreeQ[{a,b,c,d,e,p,q},x] && IntegerQ[2*m]


Int[x_^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*Sqrt[x_]])^p_.,x_Symbol] :=
  2*Subst[Int[x^(2*m+1)*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p,x],x,Sqrt[x]] /;
FreeQ[{a,b,c,d,e,p,q},x] && IntegerQ[2*m]


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcTanh[c*x^n]),u] - b*c*n*Int[SimplifyIntegrand[u*x^(n-1)/(1-c^2*x^(2*n)),x],x]] /;
FreeQ[{a,b,c,d,e,q,n},x] && NeQ[q,-1] && IntegerQ[2*m] && (IGtQ[m,0] && IGtQ[q,0] || ILtQ[m+q+1,0] && LtQ[m*q,0])


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcCoth[c*x^n]),u] - b*c*n*Int[SimplifyIntegrand[u*x^(n-1)/(1-c^2*x^(2*n)),x],x]] /;
FreeQ[{a,b,c,d,e,q,n},x] && NeQ[q,-1] && IntegerQ[2*m] && (IGtQ[m,0] && IGtQ[q,0] || ILtQ[m+q+1,0] && LtQ[m*q,0])


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x)^q*(a+b*ArcTanh[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x]


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x)^q*(a+b*ArcCoth[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^q/(2*c*q*(2*q+1)) + 
  x*(d+e*x^2)^q*(a+b*ArcTanh[c*x])/(2*q+1) + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*ArcTanh[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[q,0]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^q/(2*c*q*(2*q+1)) + 
  x*(d+e*x^2)^q*(a+b*ArcCoth[c*x])/(2*q+1) + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*ArcCoth[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[q,0]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_,x_Symbol] :=
  b*p*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p-1)/(2*c*q*(2*q+1)) + 
  x*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p/(2*q+1) + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*ArcTanh[c*x])^p,x] - 
  b^2*d*p*(p-1)/(2*q*(2*q+1))*Int[(d+e*x^2)^(q-1)*(a+b*ArcTanh[c*x])^(p-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[q,0] && GtQ[p,1]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_,x_Symbol] :=
  b*p*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p-1)/(2*c*q*(2*q+1)) + 
  x*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p/(2*q+1) + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*ArcCoth[c*x])^p,x] - 
  b^2*d*p*(p-1)/(2*q*(2*q+1))*Int[(d+e*x^2)^(q-1)*(a+b*ArcCoth[c*x])^(p-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[q,0] && GtQ[p,1]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcTanh[c_.*x_])),x_Symbol] :=
  Log[RemoveContent[a+b*ArcTanh[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCoth[c_.*x_])),x_Symbol] :=
  Log[RemoveContent[a+b*ArcCoth[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(p+1)/(b*c*d*(p+1)) /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && NeQ[p,-1]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(p+1)/(b*c*d*(p+1)) /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && NeQ[p,-1]


Int[(a_.+b_.*ArcTanh[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*(a+b*ArcTanh[c*x])*ArcTan[Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,-I*Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,I*Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[d,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*(a+b*ArcCoth[c*x])*ArcTan[Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,-I*Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,I*Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[d,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c*Sqrt[d])*Subst[Int[(a+b*x)^p*Sech[x],x],x,ArcTanh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && GtQ[d,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -x*Sqrt[1-1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^p*Csch[x],x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && GtQ[d,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTanh[c*x])^p/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCoth[c*x])^p/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTanh[c*x])^p/(2*d*(d+e*x^2)) + 
  (a+b*ArcTanh[c*x])^(p+1)/(2*b*c*d^2*(p+1)) - 
  b*c*p/2*Int[x*(a+b*ArcTanh[c*x])^(p-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcCoth[c*x])^p/(2*d*(d+e*x^2)) + 
  (a+b*ArcCoth[c*x])^(p+1)/(2*b*c*d^2*(p+1)) - 
  b*c*p/2*Int[x*(a+b*ArcCoth[c*x])^(p-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTanh[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCoth[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(q+1)/(4*c*d*(q+1)^2) -
  x*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])/(2*d*(q+1)) +
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && NeQ[q,-3/2]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(q+1)/(4*c*d*(q+1)^2) -
  x*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])/(2*d*(q+1)) +
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && NeQ[q,-3/2]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b*p*(a+b*ArcTanh[c*x])^(p-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTanh[c*x])^p/(d*Sqrt[d+e*x^2]) +
  b^2*p*(p-1)*Int[(a+b*ArcTanh[c*x])^(p-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,1]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b*p*(a+b*ArcCoth[c*x])^(p-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCoth[c*x])^p/(d*Sqrt[d+e*x^2]) +
  b^2*p*(p-1)*Int[(a+b*ArcCoth[c*x])^(p-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,1]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_,x_Symbol] :=
  -b*p*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^(p-1)/(4*c*d*(q+1)^2) -
  x*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^p/(2*d*(q+1)) +
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^p,x] +
  b^2*p*(p-1)/(4*(q+1)^2)*Int[(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && GtQ[p,1] && NeQ[q,-3/2]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_,x_Symbol] :=
  -b*p*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^(p-1)/(4*c*d*(q+1)^2) -
  x*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^p/(2*d*(q+1)) +
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^p,x] +
  b^2*p*(p-1)/(4*(q+1)^2)*Int[(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && GtQ[p,1] && NeQ[q,-3/2]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_,x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^(p+1)/(b*c*d*(p+1)) + 
  2*c*(q+1)/(b*(p+1))*Int[x*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && LtQ[p,-1]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_,x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^(p+1)/(b*c*d*(p+1)) + 
  2*c*(q+1)/(b*(p+1))*Int[x*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && LtQ[p,-1]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  d^q/c*Subst[Int[(a+b*x)^p/Cosh[x]^(2*(q+1)),x],x,ArcTanh[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && ILtQ[2*(q+1),0] && (IntegerQ[q] || GtQ[d,0])


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  d^(q+1/2)*Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(1-c^2*x^2)^q*(a+b*ArcTanh[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && ILtQ[2*(q+1),0] && Not[IntegerQ[q] || GtQ[d,0]]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  -(-d)^q/c*Subst[Int[(a+b*x)^p/Sinh[x]^(2*(q+1)),x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && ILtQ[2*(q+1),0] && IntegerQ[q]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  -(-d)^(q+1/2)*x*Sqrt[(c^2*x^2-1)/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^p/Sinh[x]^(2*(q+1)),x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && ILtQ[2*(q+1),0] && Not[IntegerQ[q]]


Int[ArcTanh[c_.*x_]/(d_.+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+c*x]/(d+e*x^2),x] - 1/2*Int[Log[1-c*x]/(d+e*x^2),x] /;
FreeQ[{c,d,e},x]


Int[ArcCoth[c_.*x_]/(d_.+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+1/(c*x)]/(d+e*x^2),x] - 1/2*Int[Log[1-1/(c*x)]/(d+e*x^2),x] /;
FreeQ[{c,d,e},x]


Int[(a_+b_.*ArcTanh[c_.*x_])/(d_.+e_.*x_^2),x_Symbol] :=
  a*Int[1/(d+e*x^2),x] + b*Int[ArcTanh[c*x]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(a_+b_.*ArcCoth[c_.*x_])/(d_.+e_.*x_^2),x_Symbol] :=
  a*Int[1/(d+e*x^2),x] + b*Int[ArcCoth[c*x]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^q,x]},  
  Dist[a+b*ArcTanh[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[q] || ILtQ[q+1/2,0])


Int[(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^q,x]},  
  Dist[a+b*ArcCoth[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[q] || ILtQ[q+1/2,0])


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[q] && IGtQ[p,0]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[q] && IGtQ[p,0]


Int[(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  Unintegrable[(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,p,q},x]


Int[(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  Unintegrable[(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,p,q},x]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  f^2/e*Int[(f*x)^(m-2)*(a+b*ArcTanh[c*x])^p,x] -
  d*f^2/e*Int[(f*x)^(m-2)*(a+b*ArcTanh[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,0] && GtQ[m,1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  f^2/e*Int[(f*x)^(m-2)*(a+b*ArcCoth[c*x])^p,x] -
  d*f^2/e*Int[(f*x)^(m-2)*(a+b*ArcCoth[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,0] && GtQ[m,1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[(f*x)^m*(a+b*ArcTanh[c*x])^p,x] -
  e/(d*f^2)*Int[(f*x)^(m+2)*(a+b*ArcTanh[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[(f*x)^m*(a+b*ArcCoth[c*x])^p,x] -
  e/(d*f^2)*Int[(f*x)^(m+2)*(a+b*ArcCoth[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,0] && LtQ[m,-1]


Int[x_*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(p+1)/(b*e*(p+1)) + 
  1/(c*d)*Int[(a+b*ArcTanh[c*x])^p/(1-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[x_*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(p+1)/(b*e*(p+1)) + 
  1/(c*d)*Int[(a+b*ArcCoth[c*x])^p/(1-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[x_*(a_.+b_.*ArcTanh[c_.*x_])^p_/(d_+e_.*x_^2),x_Symbol] :=
  x*(a+b*ArcTanh[c*x])^(p+1)/(b*c*d*(p+1)) - 
  1/(b*c*d*(p+1))*Int[(a+b*ArcTanh[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && Not[IGtQ[p,0]] && NeQ[p,-1]


Int[x_*(a_.+b_.*ArcCoth[c_.*x_])^p_/(d_+e_.*x_^2),x_Symbol] :=
  -x*(a+b*ArcCoth[c*x])^(p+1)/(b*c*d*(p+1)) - 
  1/(b*c*d*(p+1))*Int[(a+b*ArcCoth[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && Not[IGtQ[p,0]] && NeQ[p,-1]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(p+1)/(b*d*(p+1)) +
  1/d*Int[(a+b*ArcTanh[c*x])^p/(x*(1+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(p+1)/(b*d*(p+1)) +
  1/d*Int[(a+b*ArcCoth[c*x])^p/(x*(1+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,0]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTanh[c_.*x_])^p_/(d_+e_.*x_^2),x_Symbol] :=
  (f*x)^m*(a+b*ArcTanh[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*d*(p+1))*Int[(f*x)^(m-1)*(a+b*ArcTanh[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && LtQ[p,-1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCoth[c_.*x_])^p_/(d_+e_.*x_^2),x_Symbol] :=
  (f*x)^m*(a+b*ArcCoth[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*d*(p+1))*Int[(f*x)^(m-1)*(a+b*ArcCoth[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && LtQ[p,-1]


Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTanh[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[EqQ[m,1] && NeQ[a,0]]


Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCoth[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[EqQ[m,1] && NeQ[a,0]]


Int[x_*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^p/(2*e*(q+1)) + 
  b*p/(2*c*(q+1))*Int[(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,q},x] && EqQ[c^2*d+e,0] && GtQ[p,0] && NeQ[q,-1]


Int[x_*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^p/(2*e*(q+1)) +
  b*p/(2*c*(q+1))*Int[(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,q},x] && EqQ[c^2*d+e,0] && GtQ[p,0] && NeQ[q,-1]


Int[x_*(a_.+b_.*ArcTanh[c_.*x_])^p_/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTanh[c*x])^(p+1)/(b*c*d*(p+1)*(d+e*x^2)) +
  (1+c^2*x^2)*(a+b*ArcTanh[c*x])^(p+2)/(b^2*e*(p+1)*(p+2)*(d+e*x^2)) +
  4/(b^2*(p+1)*(p+2))*Int[x*(a+b*ArcTanh[c*x])^(p+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[p,-1] && NeQ[p,-2]


Int[x_*(a_.+b_.*ArcCoth[c_.*x_])^p_/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcCoth[c*x])^(p+1)/(b*c*d*(p+1)*(d+e*x^2)) +
  (1+c^2*x^2)*(a+b*ArcCoth[c*x])^(p+2)/(b^2*e*(p+1)*(p+2)*(d+e*x^2)) +
  4/(b^2*(p+1)*(p+2))*Int[x*(a+b*ArcCoth[c*x])^(p+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[p,-1] && NeQ[p,-2]


Int[x_^2*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(q+1)/(4*c^3*d*(q+1)^2) - 
  x*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])/(2*c^2*d*(q+1)) + 
  1/(2*c^2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && NeQ[q,-5/2]


Int[x_^2*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(q+1)/(4*c^3*d*(q+1)^2) - 
  x*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])/(2*c^2*d*(q+1)) + 
  1/(2*c^2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && NeQ[q,-5/2]


Int[x_^2*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  -(a+b*ArcTanh[c*x])^(p+1)/(2*b*c^3*d^2*(p+1)) + 
  x*(a+b*ArcTanh[c*x])^p/(2*c^2*d*(d+e*x^2)) - 
  b*p/(2*c)*Int[x*(a+b*ArcTanh[c*x])^(p-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,0]


Int[x_^2*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  -(a+b*ArcCoth[c*x])^(p+1)/(2*b*c^3*d^2*(p+1)) + 
  x*(a+b*ArcCoth[c*x])^p/(2*c^2*d*(d+e*x^2)) - 
  b*p/(2*c)*Int[x*(a+b*ArcCoth[c*x])^(p-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  -b*(f*x)^m*(d+e*x^2)^(q+1)/(c*d*m^2) + 
  f*(f*x)^(m-1)*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])/(c^2*d*m) - 
  f^2*(m-1)/(c^2*d*m)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && EqQ[m+2*q+2,0] && LtQ[q,-1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  -b*(f*x)^m*(d+e*x^2)^(q+1)/(c*d*m^2) + 
  f*(f*x)^(m-1)*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])/(c^2*d*m) - 
  f^2*(m-1)/(c^2*d*m)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && EqQ[m+2*q+2,0] && LtQ[q,-1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_,x_Symbol] :=
  -b*p*(f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^(p-1)/(c*d*m^2) + 
  f*(f*x)^(m-1)*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^p/(c^2*d*m) + 
  b^2*p*(p-1)/m^2*Int[(f*x)^m*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p-2),x] - 
  f^2*(m-1)/(c^2*d*m)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && EqQ[m+2*q+2,0] && LtQ[q,-1] && GtQ[p,1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_,x_Symbol] :=
  -b*p*(f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^(p-1)/(c*d*m^2) + 
  f*(f*x)^(m-1)*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^p/(c^2*d*m) + 
  b^2*p*(p-1)/m^2*Int[(f*x)^m*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p-2),x] - 
  f^2*(m-1)/(c^2*d*m)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && EqQ[m+2*q+2,0] && LtQ[q,-1] && GtQ[p,1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_,x_Symbol] :=
  (f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*(p+1))*Int[(f*x)^(m-1)*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[c^2*d+e,0] && EqQ[m+2*q+2,0] && LtQ[p,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_,x_Symbol] :=
  (f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*(p+1))*Int[(f*x)^(m-1)*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[c^2*d+e,0] && EqQ[m+2*q+2,0] && LtQ[p,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^p/(d*(m+1)) - 
  b*c*p/(m+1)*Int[(f*x)^(m+1)*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[c^2*d+e,0] && EqQ[m+2*q+3,0] && GtQ[p,0] && NeQ[m,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^p/(d*f*(m+1)) - 
  b*c*p/(f*(m+1))*Int[(f*x)^(m+1)*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[c^2*d+e,0] && EqQ[m+2*q+3,0] && GtQ[p,0] && NeQ[m,-1]


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTanh[c*x])/(f*(m+2)) - 
  b*c*d/(f*(m+2))*Int[(f*x)^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[(f*x)^m*(a+b*ArcTanh[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && NeQ[m,-2]


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCoth[c*x])/(f*(m+2)) - 
  b*c*d/(f*(m+2))*Int[(f*x)^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[(f*x)^m*(a+b*ArcCoth[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && NeQ[m,-2]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && IGtQ[q,1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && IGtQ[q,1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  d*Int[(f*x)^m*(d+e*x^2)^(q-1)*(a+b*ArcTanh[c*x])^p,x] - 
  c^2*d/f^2*Int[(f*x)^(m+2)*(d+e*x^2)^(q-1)*(a+b*ArcTanh[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[q,0] && IGtQ[p,0] && (RationalQ[m] || EqQ[p,1] && IntegerQ[q])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  d*Int[(f*x)^m*(d+e*x^2)^(q-1)*(a+b*ArcCoth[c*x])^p,x] - 
  c^2*d/f^2*Int[(f*x)^(m+2)*(d+e*x^2)^(q-1)*(a+b*ArcCoth[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[q,0] && IGtQ[p,0] && (RationalQ[m] || EqQ[p,1] && IntegerQ[q])


Int[(f_.*x_)^m_*(a_.+b_.*ArcTanh[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcTanh[c*x])^p/(c^2*d*m) + 
  b*f*p/(c*m)*Int[(f*x)^(m-1)*(a+b*ArcTanh[c*x])^(p-1)/Sqrt[d+e*x^2],x] + 
  f^2*(m-1)/(c^2*m)*Int[(f*x)^(m-2)*(a+b*ArcTanh[c*x])^p/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[p,0] && GtQ[m,1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCoth[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCoth[c*x])^p/(c^2*d*m) + 
  b*f*p/(c*m)*Int[(f*x)^(m-1)*(a+b*ArcCoth[c*x])^(p-1)/Sqrt[d+e*x^2],x] + 
  f^2*(m-1)/(c^2*m)*Int[(f*x)^(m-2)*(a+b*ArcCoth[c*x])^p/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[p,0] && GtQ[m,1]


Int[(a_.+b_.*ArcTanh[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcTanh[c*x])*ArcTanh[Sqrt[1-c*x]/Sqrt[1+c*x]] + 
  b/Sqrt[d]*PolyLog[2,-Sqrt[1-c*x]/Sqrt[1+c*x]] - 
  b/Sqrt[d]*PolyLog[2,Sqrt[1-c*x]/Sqrt[1+c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[d,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcCoth[c*x])*ArcTanh[Sqrt[1-c*x]/Sqrt[1+c*x]] + 
  b/Sqrt[d]*PolyLog[2,-Sqrt[1-c*x]/Sqrt[1+c*x]] - 
  b/Sqrt[d]*PolyLog[2,Sqrt[1-c*x]/Sqrt[1+c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[d,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  1/Sqrt[d]*Subst[Int[(a+b*x)^p*Csch[x],x],x,ArcTanh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && GtQ[d,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -c*x*Sqrt[1-1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^p*Sech[x],x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && GtQ[d,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTanh[c*x])^p/(x*Sqrt[1-c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCoth[c*x])^p/(x*Sqrt[1-c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcTanh[c*x])^p/(d*x) + 
  b*c*p*Int[(a+b*ArcTanh[c*x])^(p-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcCoth[c*x])^p/(d*x) + 
  b*c*p*Int[(a+b*ArcCoth[c*x])^(p-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[p,0]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTanh[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTanh[c*x])^p/(d*f*(m+1)) - 
  b*c*p/(f*(m+1))*Int[(f*x)^(m+1)*(a+b*ArcTanh[c*x])^(p-1)/Sqrt[d+e*x^2],x] + 
  c^2*(m+2)/(f^2*(m+1))*Int[(f*x)^(m+2)*(a+b*ArcTanh[c*x])^p/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[p,0] && LtQ[m,-1] && NeQ[m,-2]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCoth[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCoth[c*x])^p/(d*f*(m+1)) - 
  b*c*p/(f*(m+1))*Int[(f*x)^(m+1)*(a+b*ArcCoth[c*x])^(p-1)/Sqrt[d+e*x^2],x] + 
  c^2*(m+2)/(f^2*(m+1))*Int[(f*x)^(m+2)*(a+b*ArcCoth[c*x])^p/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[p,0] && LtQ[m,-1] && NeQ[m,-2]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^p,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegersQ[p,2*q] && LtQ[q,-1] && IGtQ[m,1] && NeQ[p,-1]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^p,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegersQ[p,2*q] && LtQ[q,-1] && IGtQ[m,1] && NeQ[p,-1]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^p,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegersQ[p,2*q] && LtQ[q,-1] && ILtQ[m,0] && NeQ[p,-1]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^p,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegersQ[p,2*q] && LtQ[q,-1] && ILtQ[m,0] && NeQ[p,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  (f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*(p+1))*Int[(f*x)^(m-1)*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p+1),x] + 
  c*(m+2*q+2)/(b*f*(p+1))*Int[(f*x)^(m+1)*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && LtQ[p,-1] && NeQ[m+2*q+2,0] && RationalQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  (f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*(p+1))*Int[(f*x)^(m-1)*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p+1),x] + 
  c*(m+2*q+2)/(b*f*(p+1))*Int[(f*x)^(m+1)*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && LtQ[q,-1] && LtQ[p,-1] && NeQ[m+2*q+2,0] && RationalQ[m]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  d^q/c^(m+1)*Subst[Int[(a+b*x)^p*Sinh[x]^m/Cosh[x]^(m+2*(q+1)),x],x,ArcTanh[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && ILtQ[m+2*q+1,0] && (IntegerQ[q] || GtQ[d,0])


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  d^(q+1/2)*Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[x^m*(1-c^2*x^2)^q*(a+b*ArcTanh[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && ILtQ[m+2*q+1,0] && Not[IntegerQ[q] || GtQ[d,0]]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  -(-d)^q/c^(m+1)*Subst[Int[(a+b*x)^p*Cosh[x]^m/Sinh[x]^(m+2*(q+1)),x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && ILtQ[m+2*q+1,0] && IntegerQ[q]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  -(-d)^(q+1/2)*x*Sqrt[(c^2*x^2-1)/(c^2*x^2)]/(c^m*Sqrt[d+e*x^2])*Subst[Int[(a+b*x)^p*Cosh[x]^m/Sinh[x]^(m+2*(q+1)),x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && ILtQ[m+2*q+1,0] && Not[IntegerQ[q]]


Int[x_*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcTanh[c*x])/(2*e*(q+1)) - 
  b*c/(2*e*(q+1))*Int[(d+e*x^2)^(q+1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]


Int[x_*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcCoth[c*x])/(2*e*(q+1)) - 
  b*c/(2*e*(q+1))*Int[(d+e*x^2)^(q+1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^q,x]},  
  Dist[a+b*ArcTanh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && (
  IGtQ[q,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*q+3,0]] || 
  IGtQ[(m+1)/2,0] && Not[ILtQ[q,0] && GtQ[m+2*q+3,0]] || 
  ILtQ[(m+2*q+1)/2,0] && Not[ILtQ[(m-1)/2,0]] )


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^q,x]},  
  Dist[a+b*ArcCoth[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && (
  IGtQ[q,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*q+3,0]] || 
  IGtQ[(m+1)/2,0] && Not[ILtQ[q,0] && GtQ[m+2*q+3,0]] || 
  ILtQ[(m+2*q+1)/2,0] && Not[ILtQ[(m-1)/2,0]] )


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTanh[c*x])^p,(f*x)^m*(d+e*x^2)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[q] && IGtQ[p,0] && (GtQ[q,0] || LtQ[q,-1] && IntegerQ[m] && NeQ[m,1])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCoth[c*x])^p,(f*x)^m*(d+e*x^2)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[q] && IGtQ[p,0] && (GtQ[q,0] || LtQ[q,-1] && IntegerQ[m] && NeQ[m,1])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  a*Int[(f*x)^m*(d+e*x^2)^q,x] + b*Int[(f*x)^m*(d+e*x^2)^q*ArcTanh[c*x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  a*Int[(f*x)^m*(d+e*x^2)^q,x] + b*Int[(f*x)^m*(d+e*x^2)^q*ArcCoth[c*x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x^2)^q*(a+b*ArcTanh[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x]


Int[x_^m_.*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_.,x_Symbol] :=
  Unintegrable[x^m*(d+e*x^2)^q*(a+b*ArcCoth[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,m,p,q},x]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTanh[c*x])^p/(d+e*x^2),(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && IGtQ[m,0]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCoth[c*x])^p/(d+e*x^2),(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && IGtQ[m,0]


Int[ArcTanh[u_]*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTanh[c*x])^p/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTanh[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[u^2-(1-2/(1+c*x))^2,0]


Int[ArcCoth[u_]*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCoth[c*x])^p/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCoth[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[u^2-(1-2/(1+c*x))^2,0]


Int[ArcTanh[u_]*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTanh[c*x])^p/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTanh[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[u^2-(1-2/(1-c*x))^2,0]


Int[ArcCoth[u_]*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCoth[c*x])^p/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCoth[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[u^2-(1-2/(1-c*x))^2,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_.*Log[f_+g_.*x_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(p+1)*Log[f+g*x]/(b*c*d*(p+1)) - 
  g/(b*c*d*(p+1))*Int[(a+b*ArcTanh[c*x])^(p+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[c^2*f^2-g^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_.*Log[f_+g_.*x_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(p+1)*Log[f+g*x]/(b*c*d*(p+1)) - 
  g/(b*c*d*(p+1))*Int[(a+b*ArcCoth[c*x])^(p+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[c^2*f^2-g^2,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^p*PolyLog[2,1-u]/(2*c*d) - 
  b*p/2*Int[(a+b*ArcTanh[c*x])^(p-1)*PolyLog[2,1-u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[(1-u)^2-(1-2/(1+c*x))^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^p*PolyLog[2,1-u]/(2*c*d) - 
  b*p/2*Int[(a+b*ArcCoth[c*x])^(p-1)*PolyLog[2,1-u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[(1-u)^2-(1-2/(1+c*x))^2,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcTanh[c*x])^p*PolyLog[2,1-u]/(2*c*d) + 
  b*p/2*Int[(a+b*ArcTanh[c*x])^(p-1)*PolyLog[2,1-u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[(1-u)^2-(1-2/(1-c*x))^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCoth[c*x])^p*PolyLog[2,1-u]/(2*c*d) + 
  b*p/2*Int[(a+b*ArcCoth[c*x])^(p-1)*PolyLog[2,1-u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[(1-u)^2-(1-2/(1-c*x))^2,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_.*PolyLog[k_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcTanh[c*x])^p*PolyLog[k+1,u]/(2*c*d) +
  b*p/2*Int[(a+b*ArcTanh[c*x])^(p-1)*PolyLog[k+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,k},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[u^2-(1-2/(1+c*x))^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_.*PolyLog[k_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCoth[c*x])^p*PolyLog[k+1,u]/(2*c*d) +
  b*p/2*Int[(a+b*ArcCoth[c*x])^(p-1)*PolyLog[k+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,k},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[u^2-(1-2/(1+c*x))^2,0]


Int[(a_.+b_.*ArcTanh[c_.*x_])^p_.*PolyLog[k_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^p*PolyLog[k+1,u]/(2*c*d) -
  b*p/2*Int[(a+b*ArcTanh[c*x])^(p-1)*PolyLog[k+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,k},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[u^2-(1-2/(1-c*x))^2,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^p_.*PolyLog[k_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^p*PolyLog[k+1,u]/(2*c*d) -
  b*p/2*Int[(a+b*ArcCoth[c*x])^(p-1)*PolyLog[k+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,k},x] && IGtQ[p,0] && EqQ[c^2*d+e,0] && EqQ[u^2-(1-2/(1-c*x))^2,0]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCoth[c_.*x_])*(a_.+b_.*ArcTanh[c_.*x_])),x_Symbol] :=
  (-Log[a+b*ArcCoth[c*x]]+Log[a+b*ArcTanh[c*x]])/(b^2*c*d*(ArcCoth[c*x]-ArcTanh[c*x])) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0]


Int[(a_.+b_.*ArcCoth[c_.*x_])^m_.*(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(m+1)*(a+b*ArcTanh[c*x])^p/(b*c*d*(m+1)) -
  p/(m+1)*Int[(a+b*ArcCoth[c*x])^(m+1)*(a+b*ArcTanh[c*x])^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && IGeQ[m,p]


Int[(a_.+b_.*ArcTanh[c_.*x_])^m_.*(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(m+1)*(a+b*ArcCoth[c*x])^p/(b*c*d*(m+1)) -
  p/(m+1)*Int[(a+b*ArcTanh[c*x])^(m+1)*(a+b*ArcCoth[c*x])^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && IGtQ[m,p]


Int[ArcTanh[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+a*x]/(c+d*x^n),x] -
  1/2*Int[Log[1-a*x]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[EqQ[n,2] && EqQ[a^2*c+d,0]]


Int[ArcCoth[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+1/(a*x)]/(c+d*x^n),x] -
  1/2*Int[Log[1-1/(a*x)]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[EqQ[n,2] && EqQ[a^2*c+d,0]]


Int[Log[d_.*x_^m_.]*ArcTanh[c_.*x_^n_.]/x_,x_Symbol] :=
  1/2*Int[Log[d*x^m]*Log[1+c*x^n]/x,x] - 1/2*Int[Log[d*x^m]*Log[1-c*x^n]/x,x] /;
FreeQ[{c,d,m,n},x]


Int[Log[d_.*x_^m_.]*ArcCoth[c_.*x_^n_.]/x_,x_Symbol] :=
  1/2*Int[Log[d*x^m]*Log[1+1/(c*x^n)]/x,x] - 1/2*Int[Log[d*x^m]*Log[1-1/(c*x^n)]/x,x] /;
FreeQ[{c,d,m,n},x]


Int[Log[d_.*x_^m_.]*(a_+b_.*ArcTanh[c_.*x_^n_.])/x_,x_Symbol] :=
  a*Int[Log[d*x^m]/x,x] + b*Int[(Log[d*x^m]*ArcTanh[c*x^n])/x,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[Log[d_.*x_^m_.]*(a_+b_.*ArcCoth[c_.*x_^n_.])/x_,x_Symbol] :=
  a*Int[Log[d*x^m]/x,x] + b*Int[(Log[d*x^m]*ArcCoth[c*x^n])/x,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  x*(d+e*Log[f+g*x^2])*(a+b*ArcTanh[c*x]) - 
  2*e*g*Int[x^2*(a+b*ArcTanh[c*x])/(f+g*x^2),x] - 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  x*(d+e*Log[f+g*x^2])*(a+b*ArcCoth[c*x]) - 
  2*e*g*Int[x^2*(a+b*ArcCoth[c*x])/(f+g*x^2),x] - 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[Log[f_.+g_.*x_^2]*ArcTanh[c_.*x_]/x_,x_Symbol] :=
  (Log[f+g*x^2]-Log[1-c*x]-Log[1+c*x])*Int[ArcTanh[c*x]/x,x] - 1/2*Int[Log[1-c*x]^2/x,x] + 1/2*Int[Log[1+c*x]^2/x,x] /;
FreeQ[{c,f,g},x] && EqQ[c^2*f+g,0]


Int[Log[f_.+g_.*x_^2]*ArcCoth[c_.*x_]/x_,x_Symbol] :=
  (Log[f+g*x^2]-Log[-c^2*x^2]-Log[1-1/(c*x)]-Log[1+1/(c*x)])*Int[ArcCoth[c*x]/x,x] + 
  Int[Log[-c^2*x^2]*ArcCoth[c*x]/x,x] - 
  1/2*Int[Log[1-1/(c*x)]^2/x,x] + 
  1/2*Int[Log[1+1/(c*x)]^2/x,x] /;
FreeQ[{c,f,g},x] && EqQ[c^2*f+g,0]


Int[Log[f_.+g_.*x_^2]*(a_+b_.*ArcTanh[c_.*x_])/x_,x_Symbol] :=
  a*Int[Log[f+g*x^2]/x,x] + b*Int[Log[f+g*x^2]*ArcTanh[c*x]/x,x] /;
FreeQ[{a,b,c,f,g},x]


Int[Log[f_.+g_.*x_^2]*(a_+b_.*ArcCoth[c_.*x_])/x_,x_Symbol] :=
  a*Int[Log[f+g*x^2]/x,x] + b*Int[Log[f+g*x^2]*ArcCoth[c*x]/x,x] /;
FreeQ[{a,b,c,f,g},x]


Int[(d_+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTanh[c_.*x_])/x_,x_Symbol] :=
  d*Int[(a+b*ArcTanh[c*x])/x,x] + e*Int[Log[f+g*x^2]*(a+b*ArcTanh[c*x])/x,x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[(d_+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCoth[c_.*x_])/x_,x_Symbol] :=
  d*Int[(a+b*ArcCoth[c*x])/x,x] + e*Int[Log[f+g*x^2]*(a+b*ArcCoth[c*x])/x,x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  x^(m+1)*(d+e*Log[f+g*x^2])*(a+b*ArcTanh[c*x])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcTanh[c*x])/(f+g*x^2),x] - 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m/2,0]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  x^(m+1)*(d+e*Log[f+g*x^2])*(a+b*ArcCoth[c*x])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcCoth[c*x])/(f+g*x^2),x] - 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m/2,0]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*Log[f+g*x^2]),x]},  
  Dist[a+b*ArcTanh[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[(m+1)/2,0]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*Log[f+g*x^2]),x]},  
  Dist[a+b*ArcCoth[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[(m+1)/2,0]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(a+b*ArcTanh[c*x]),x]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && NeQ[m,-1]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(a+b*ArcCoth[c*x]),x]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && NeQ[m,-1]


Int[x_*(d_.+e_.*Log[f_+g_.*x_^2])*(a_.+b_.*ArcTanh[c_.*x_])^2,x_Symbol] :=
  (f+g*x^2)*(d+e*Log[f+g*x^2])*(a+b*ArcTanh[c*x])^2/(2*g) - 
  e*x^2*(a+b*ArcTanh[c*x])^2/2 + 
  b/c*Int[(d+e*Log[f+g*x^2])*(a+b*ArcTanh[c*x]),x] + 
  b*c*e*Int[x^2*(a+b*ArcTanh[c*x])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*f+g,0]


Int[x_*(d_.+e_.*Log[f_+g_.*x_^2])*(a_.+b_.*ArcCoth[c_.*x_])^2,x_Symbol] :=
  (f+g*x^2)*(d+e*Log[f+g*x^2])*(a+b*ArcCoth[c*x])^2/(2*g) - 
  e*x^2*(a+b*ArcCoth[c*x])^2/2 + 
  b/c*Int[(d+e*Log[f+g*x^2])*(a+b*ArcCoth[c*x]),x] + 
  b*c*e*Int[x^2*(a+b*ArcCoth[c*x])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*f+g,0]





(* ::Subsection::Closed:: *)
(*7.2.2 u (a+b arctanh(c+d x))^p*)


Int[(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcTanh[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(a+b*ArcTanh[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]


Int[(a_.+b_.*ArcCoth[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(a+b*ArcCoth[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(f*x/d)^m*(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(f*x/d)^m*(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcTanh[c+d*x])^p/(f*(m+1)) - 
  b*d*p/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcTanh[c+d*x])^(p-1)/(1-(c+d*x)^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[m,-1]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcCoth[c+d*x])^p/(f*(m+1)) - 
  b*d*p/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcCoth[c+d*x])^(p-1)/(1-(c+d*x)^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[m,-1]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(e+f*x)^m*(a+b*ArcTanh[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(e+f*x)^m*(a+b*ArcCoth[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]


Int[ArcTanh[c_+d_.*x_]/(e_+f_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+c+d*x]/(e+f*x^n),x] -
  1/2*Int[Log[1-c-d*x]/(e+f*x^n),x] /;
FreeQ[{c,d,e,f},x] && RationalQ[n]


Int[ArcCoth[c_+d_.*x_]/(e_+f_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[(1+c+d*x)/(c+d*x)]/(e+f*x^n),x] -
  1/2*Int[Log[(-1+c+d*x)/(c+d*x)]/(e+f*x^n),x] /;
FreeQ[{c,d,e,f},x] && RationalQ[n]


Int[ArcTanh[c_+d_.*x_]/(e_+f_.*x_^n_),x_Symbol] :=
  Unintegrable[ArcTanh[c+d*x]/(e+f*x^n),x] /;
FreeQ[{c,d,e,f,n},x] && Not[RationalQ[n]]


Int[ArcCoth[c_+d_.*x_]/(e_+f_.*x_^n_),x_Symbol] :=
  Unintegrable[ArcCoth[c+d*x]/(e+f*x^n),x] /;
FreeQ[{c,d,e,f,n},x] && Not[RationalQ[n]]


Int[(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^q*(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,p,q},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^q*(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,p,q},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^q*(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,p,q},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^q*(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,p,q},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]





(* ::Subsection::Closed:: *)
(*7.2.3 Exponentials of inverse hyperbolic tangent*)


Int[E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[((1+a*x)^((n+1)/2)/((1-a*x)^((n-1)/2)*Sqrt[1-a^2*x^2])),x] /;
FreeQ[a,x] && IntegerQ[(n-1)/2]


Int[x_^m_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[x^m*((1+a*x)^((n+1)/2)/((1-a*x)^((n-1)/2)*Sqrt[1-a^2*x^2])),x] /;
FreeQ[{a,m},x] && IntegerQ[(n-1)/2]


Int[E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,n},x] && Not[IntegerQ[(n-1)/2]]


Int[x_^m_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[x^m*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[(n-1)/2]]


Int[(c_+d_.*x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^n*Int[(c+d*x)^(p-n)*(1-a^2*x^2)^(n/2),x] /;
FreeQ[{a,c,d,p},x] && EqQ[a*c+d,0] && IntegerQ[(n-1)/2] && IntegerQ[2*p]


Int[(e_.+f_.*x_)^m_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^n*Int[(e+f*x)^m*(c+d*x)^(p-n)*(1-a^2*x^2)^(n/2),x] /;
FreeQ[{a,c,d,e,f,m,p},x] && EqQ[a*c+d,0] && IntegerQ[(n-1)/2] && (IntegerQ[p] || EqQ[p,n/2] || EqQ[p-n/2-1,0]) && IntegerQ[2*p]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1+d*x/c)^p*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2-d^2,0] && (IntegerQ[p] || GtQ[c,0])


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[u*(c+d*x)^p*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2-d^2,0] && Not[IntegerQ[p] || GtQ[c,0]]


Int[u_.*(c_+d_./x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  d^p*Int[u*(1+c*x/d)^p*E^(n*ArcTanh[a*x])/x^p,x] /;
FreeQ[{a,c,d,n},x] && EqQ[c^2-a^2*d^2,0] && IntegerQ[p]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*c^p*Int[u*(1+d/(c*x))^p*(1+1/(a*x))^(n/2)/(1-1/(a*x))^(n/2),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c^2-a^2*d^2,0] && Not[IntegerQ[p]] && IntegerQ[n/2] && GtQ[c,0]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[u*(c+d/x)^p*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c^2-a^2*d^2,0] && Not[IntegerQ[p]] && IntegerQ[n/2] && Not[GtQ[c,0]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  x^p*(c+d/x)^p/(1+c*x/d)^p*Int[u*(1+c*x/d)^p*E^(n*ArcTanh[a*x])/x^p,x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2-a^2*d^2,0] && Not[IntegerQ[p]]


Int[E^(n_*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n-a*x)*E^(n*ArcTanh[a*x])/(a*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n]]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a*c*(n^2-4*(p+1)^2)) - 
  2*(p+1)*(2*p+3)/(c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && LtQ[p,-1] && Not[IntegerQ[n]] && NeQ[n^2-4*(p+1)^2,0] && IntegerQ[2*p]


Int[E^(n_.*ArcTanh[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcTanh[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-a^2*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,p},x] && EqQ[a^2*c+d,0] && IntegerQ[p] && IGtQ[(n+1)/2,0] && Not[IntegerQ[p-n/2]]


Int[(c_+d_.*x_^2)^p_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-a^2*x^2)^(p+n/2)/(1-a*x)^n,x] /;
FreeQ[{a,c,d,p},x] && EqQ[a^2*c+d,0] && IntegerQ[p] && ILtQ[(n-1)/2,0] && Not[IntegerQ[p-n/2]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c+d,0] && (IntegerQ[p] || GtQ[c,0])


Int[(c_+d_.*x_^2)^p_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(n/2)*Int[(c+d*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[p] || GtQ[c,0]] && IGtQ[n/2,0]


Int[(c_+d_.*x_^2)^p_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  1/c^(n/2)*Int[(c+d*x^2)^(p+n/2)/(1-a*x)^n,x] /;
FreeQ[{a,c,d,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[p] || GtQ[c,0]] && ILtQ[n/2,0]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1-a^2*x^2)^FracPart[p]*Int[(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[p] || GtQ[c,0]]


Int[x_*E^(n_*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (1-a*n*x)*E^(n*ArcTanh[a*x])/(d*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(2*d*(p+1)) - a*c*n/(2*d*(p+1))*Int[(c+d*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && LtQ[p,-1] && Not[IntegerQ[n]] && IntegerQ[2*p]


(* Int[x_*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  -(2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(d*(n^2-4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && LeQ[p,-1] && NeQ[n^2-4*(p+1)^2,0] && Not[IntegerQ[n]] *)


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (1-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a*d*n*(n^2-1)) /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && EqQ[n^2+2*(p+1),0] && Not[IntegerQ[n]]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  -(n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a*d*(n^2-4*(p+1)^2)) + 
  (n^2+2*(p+1))/(d*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && LtQ[p,-1] && Not[IntegerQ[n]] && NeQ[n^2-4*(p+1)^2,0] && IntegerQ[2*p]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1-a^2*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[a^2*c+d,0] && (IntegerQ[p] || GtQ[c,0]) && IGtQ[(n+1)/2,0] && Not[IntegerQ[p-n/2]]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1-a^2*x^2)^(p+n/2)/(1-a*x)^n,x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[a^2*c+d,0] && (IntegerQ[p] || GtQ[c,0]) && ILtQ[(n-1)/2,0] && Not[IntegerQ[p-n/2]]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[a^2*c+d,0] && (IntegerQ[p] || GtQ[c,0])


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(n/2)*Int[x^m*(c+d*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[p] || GtQ[c,0]] && IGtQ[n/2,0]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  1/c^(n/2)*Int[x^m*(c+d*x^2)^(p+n/2)/(1-a*x)^n,x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[p] || GtQ[c,0]] && ILtQ[n/2,0]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1-a^2*x^2)^FracPart[p]*Int[x^m*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[p] || GtQ[c,0]] && Not[IntegerQ[n/2]]


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c+d,0] && (IntegerQ[p] || GtQ[c,0])


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/((1-a*x)^FracPart[p]*(1+a*x)^FracPart[p])*
    Int[u*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[p] || GtQ[c,0]] && IntegerQ[n/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1-a^2*x^2)^FracPart[p]*Int[u*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[p] || GtQ[c,0]] && Not[IntegerQ[n/2]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^(2*p)*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[c+a^2*d,0] && IntegerQ[p]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-1/(a*x))^p*(1+1/(a*x))^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c+a^2*d,0] && Not[IntegerQ[p]] && IntegerQ[n/2] && GtQ[c,0]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/((1-a*x)^p*(1+a*x)^p)*Int[u/x^(2*p)*(1-a*x)^p*(1+a*x)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c+a^2*d,0] && Not[IntegerQ[p]] && IntegerQ[n/2] && Not[GtQ[c,0]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/(1+c*x^2/d)^p*Int[u/x^(2*p)*(1+c*x^2/d)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c+a^2*d,0] && Not[IntegerQ[p]] && Not[IntegerQ[n/2]]


Int[E^(n_.*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(1+a*c+b*c*x)^(n/2)/(1-a*c-b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,n},x]


Int[x_^m_*E^(n_*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/n)*(-1-a*c+(1-a*c)*x^(2/n))^m/(1+x^(2/n))^(m+2),x],x,(1+c*(a+b*x))^(n/2)/(1-c*(a+b*x))^(n/2)] /;
FreeQ[{a,b,c},x] && ILtQ[m,0] && LtQ[-1,n,1]


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(d+e*x)^m*(1+a*c+b*c*x)^(n/2)/(1-a*c-b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTanh[a_+b_.*x_]),x_Symbol] :=
  (c/(1-a^2))^p*Int[u*(1-a-b*x)^(p-n/2)*(1+a+b*x)^(p+n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d-2*a*e,0] && EqQ[b^2*c+e(1-a^2),0] && (IntegerQ[p] || GtQ[c/(1-a^2),0])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTanh[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1-a^2-2*a*b*x-b^2*x^2)^p*Int[u*(1-a^2-2*a*b*x-b^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d-2*a*e,0] && EqQ[b^2*c+e(1-a^2),0] && Not[IntegerQ[p] || GtQ[c/(1-a^2),0]]


Int[u_.*E^(n_.*ArcTanh[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcCoth[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*Int[u*E^(n*ArcTanh[a*x]),x] /;
FreeQ[a,x] && IntegerQ[n/2]


Int[E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^((n+1)/2)/(x^2*(1-x/a)^((n-1)/2)*Sqrt[1-x^2/a^2]),x],x,1/x] /;
FreeQ[a,x] && IntegerQ[(n-1)/2]


Int[x_^m_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^((n+1)/2)/(x^(m+2)*(1-x/a)^((n-1)/2)*Sqrt[1-x^2/a^2]),x],x,1/x] /;
FreeQ[a,x] && IntegerQ[(n-1)/2] && IntegerQ[m]


Int[E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^(n/2)/(x^2*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[n]]


Int[x_^m_.*E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[x_^m_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -x^m*(1/x)^m*Subst[Int[(1+x/a)^((n+1)/2)/(x^(m+2)*(1-x/a)^((n-1)/2)*Sqrt[1-x^2/a^2]),x],x,1/x] /;
FreeQ[{a,m},x] && IntegerQ[(n-1)/2] && Not[IntegerQ[m]]


Int[x_^m_*E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  -x^m*(1/x)^m*Subst[Int[(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[n]] && Not[IntegerQ[m]]


Int[(c_+d_.*x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (1+a*x)*(c+d*x)^p*E^(n*ArcCoth[a*x])/(a*(p+1)) /;
FreeQ[{a,c,d,n,p},x] && EqQ[a*c+d,0] && EqQ[p,n/2] && Not[IntegerQ[n/2]]


(* Int[(c_+d_.*x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(-a)^n*c^n*Subst[Int[(d+c*x)^(p-n)*(1-x^2/a^2)^(n/2)/x^(p+2),x],x,1/x] /;
FreeQ[{a,c,d},x] && EqQ[a*c+d,0] && IntegerQ[(n-1)/2] && IntegerQ[p] *)


(* Int[x_^m_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(-a)^n*c^n*Subst[Int[(d+c*x)^(p-n)*(1-x^2/a^2)^(n/2)/x^(m+p+2),x],x,1/x] /;
FreeQ[{a,c,d},x] && EqQ[a*c+d,0] && IntegerQ[(n-1)/2] && IntegerQ[m] && IntegerQ[p] *)


(* Int[(c_+d_.*x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(-a)^n*c^n*Sqrt[c+d*x]/(Sqrt[x]*Sqrt[d+c/x])*Subst[Int[(d+c*x)^(p-n)*(1-x^2/a^2)^(n/2)/x^(p+2),x],x,1/x] /;
FreeQ[{a,c,d},x] && EqQ[a*c+d,0] && IntegerQ[(n-1)/2] && IntegerQ[p-1/2] *)


(* Int[x_^m_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(-a)^n*c^n*Sqrt[c+d*x]/(Sqrt[x]*Sqrt[d+c/x])*Subst[Int[(d+c*x)^(p-n)*(1-x^2/a^2)^(n/2)/x^(m+p+2),x],x,1/x] /;
FreeQ[{a,c,d},x] && EqQ[a*c+d,0] && IntegerQ[(n-1)/2] && IntegerQ[m] && IntegerQ[p-1/2] *)


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c^2-d^2,0] && Not[IntegerQ[n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(x^p*(1+c/(d*x))^p)*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2-d^2,0] && Not[IntegerQ[n/2]] && Not[IntegerQ[p]]


Int[(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^n*Subst[Int[(c+d*x)^(p-n)*(1-x^2/a^2)^(n/2)/x^2,x],x,1/x] /;
FreeQ[{a,c,d,p},x] && EqQ[c+a*d,0] && IntegerQ[(n-1)/2] && (IntegerQ[p] || EqQ[p,n/2] || EqQ[p,n/2+1]) && IntegerQ[2*p]


Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^n*Subst[Int[(c+d*x)^(p-n)*(1-x^2/a^2)^(n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,p},x] && EqQ[c+a*d,0] && IntegerQ[(n-1)/2] && IntegerQ[m] && (IntegerQ[p] || EqQ[p,n/2] || EqQ[p,n/2+1] || LtQ[-5,m,-1]) && IntegerQ[2*p]


Int[(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^2*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2-a^2*d^2,0] && Not[IntegerQ[n/2]] && (IntegerQ[p] || GtQ[c,0])


Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2-a^2*d^2,0] && Not[IntegerQ[n/2]] && (IntegerQ[p] || GtQ[c,0]) && IntegerQ[m]


Int[x_^m_*(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[c^2-a^2*d^2,0] && Not[IntegerQ[n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[u*(1+d/(c*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2-a^2*d^2,0] && Not[IntegerQ[n/2]] && Not[IntegerQ[p] || GtQ[c,0]]


Int[E^(n_.*ArcCoth[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcCoth[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]]


Int[E^(n_*ArcCoth[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n-a*x)*E^(n*ArcCoth[a*x])/(a*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a*c*(n^2-4*(p+1)^2)) - 
  2*(p+1)*(2*p+3)/(c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]] && LtQ[p,-1] && NeQ[p,-3/2] && NeQ[n^2-4*(p+1)^2,0] && (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_*E^(n_*ArcCoth[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcCoth[a*x])/(a^2*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^2*c*(n^2-4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]] && LeQ[p,-1] && NeQ[p,-3/2] && NeQ[n^2-4*(p+1)^2,0] && (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^3*c*n^2*(n^2-1)) /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]] && EqQ[n^2+2*(p+1),0] && NeQ[n^2,1]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^3*c*(n^2-4*(p+1)^2)) - 
  (n^2+2*(p+1))/(a^2*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]] && LeQ[p,-1] && NeQ[n^2+2*(p+1),0] && NeQ[n^2-4*(p+1)^2,0] && 
  (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(-c)^p/a^(m+1)*Subst[Int[E^(n*x)*Coth[x]^(m+2*(p+1))/Cosh[x]^(2*(p+1)),x],x,ArcCoth[a*x]] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]] && IntegerQ[m] && LeQ[3,m,-2(p+1)] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^(2*p)*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(x^(2*p)*(1-1/(a^2*x^2))^p)*Int[u*x^(2*p)*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c+d,0] && Not[IntegerQ[n/2]] && Not[IntegerQ[p]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  c^p/a^(2*p)*Int[u/x^(2*p)*(-1+a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c+a^2*d,0] && Not[IntegerQ[n/2]] && (IntegerQ[p] || GtQ[c,0]) && IntegersQ[2*p,p+n/2]


Int[(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^2,x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c+a^2*d,0] && Not[IntegerQ[n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegersQ[2*p,p+n/2]]


Int[x_^m_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c+a^2*d,0] && Not[IntegerQ[n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegersQ[2*p,p+n/2]] && IntegerQ[m]


Int[x_^m_*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[c+a^2*d,0] && Not[IntegerQ[n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegersQ[2*p,p+n/2]] && Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d/x^2)^FracPart[p]/(1-1/(a^2*x^2))^FracPart[p]*Int[u*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c+a^2*d,0] && Not[IntegerQ[n/2]] && Not[IntegerQ[p] || GtQ[c,0]]


Int[u_.*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (-1)^(n/2)*Int[u*E^(n*ArcTanh[c*(a+b*x)]),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n/2]


Int[E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (c*(a+b*x))^(n/2)*(1+1/(c*(a+b*x)))^(n/2)/(1+a*c+b*c*x)^(n/2)*Int[(1+a*c+b*c*x)^(n/2)/(-1+a*c+b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n/2]]


Int[x_^m_*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  -4/(n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/n)*(1+a*c+(1-a*c)*x^(2/n))^m/(-1+x^(2/n))^(m+2),x],x,(1+1/(c*(a+b*x)))^(n/2)/(1-1/(c*(a+b*x)))^(n/2)] /;
FreeQ[{a,b,c},x] && ILtQ[m,0] && LtQ[-1,n,1]


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (c*(a+b*x))^(n/2)*(1+1/(c*(a+b*x)))^(n/2)/(1+a*c+b*c*x)^(n/2)*Int[(d+e*x)^m*(1+a*c+b*c*x)^(n/2)/(-1+a*c+b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[n/2]]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCoth[a_+b_.*x_]),x_Symbol] :=
  (c/(1-a^2))^p*((a+b*x)/(1+a+b*x))^(n/2)*((1+a+b*x)/(a+b*x))^(n/2)*((1-a-b*x)^(n/2)/(-1+a+b*x)^(n/2))*
    Int[u*(1-a-b*x)^(p-n/2)*(1+a+b*x)^(p+n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[n/2]] && EqQ[b*d-2*a*e,0] && EqQ[b^2*c+e(1-a^2),0] && (IntegerQ[p] || GtQ[c/(1-a^2),0])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCoth[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1-a^2-2*a*b*x-b^2*x^2)^p*Int[u*(1-a^2-2*a*b*x-b^2*x^2)^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[n/2]] && EqQ[b*d-2*a*e,0] && EqQ[b^2*c+e(1-a^2),0] && Not[IntegerQ[p] || GtQ[c/(1-a^2),0]]


Int[u_.*E^(n_.*ArcCoth[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcTanh[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*7.2.4 Miscellaneous inverse hyperbolic tangent*)
(**)


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
FreeQ[{a,b},x] && RationalQ[m,n] && NeQ[m,-1] && NeQ[m+1,n]


Int[x_^m_.*ArcCoth[a_+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*ArcCoth[a+b*x^n]/(m+1) - 
  b*n/(m+1)*Int[x^(m+n)/(1-a^2-2*a*b*x^n-b^2*x^(2*n)),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && NeQ[m,-1] && NeQ[m+1,n]


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
FreeQ[{a,b,c,d,f},x] && IGtQ[m,0]


Int[x_^m_.*ArcCoth[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  1/2*Int[x^m*Log[1+1/(a+b*f^(c+d*x))],x] - 
  1/2*Int[x^m*Log[1-1/(a+b*f^(c+d*x))],x] /;
FreeQ[{a,b,c,d,f},x] && IGtQ[m,0]


Int[u_.*ArcTanh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCoth[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCoth[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcTanh[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
  x*ArcTanh[(c*x)/Sqrt[a+b*x^2]] - c*Int[x/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c},x] && EqQ[b,c^2]


Int[ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
  x*ArcCoth[(c*x)/Sqrt[a+b*x^2]] - c*Int[x/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c},x] && EqQ[b,c^2]


Int[ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]/x_,x_Symbol] :=
  ArcTanh[c*x/Sqrt[a+b*x^2]]*Log[x] - c*Int[Log[x]/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c},x] && EqQ[b,c^2]


Int[ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]/x_,x_Symbol] :=
  ArcCoth[c*x/Sqrt[a+b*x^2]]*Log[x] - c*Int[Log[x]/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c},x] && EqQ[b,c^2]


Int[(d_.*x_)^m_.*ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
  (d*x)^(m+1)*ArcTanh[(c*x)/Sqrt[a+b*x^2]]/(d*(m+1)) - c/(d*(m+1))*Int[(d*x)^(m+1)/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[b,c^2] && NeQ[m,-1]


Int[(d_.*x_)^m_.*ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
  (d*x)^(m+1)*ArcCoth[(c*x)/Sqrt[a+b*x^2]]/(d*(m+1)) - c/(d*(m+1))*Int[(d*x)^(m+1)/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[b,c^2] && NeQ[m,-1]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  1/c*Log[ArcTanh[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && EqQ[b,c^2]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  -1/c*Log[ArcCoth[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && EqQ[b,c^2]


Int[ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  ArcTanh[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && EqQ[b,c^2] && NeQ[m,-1]


Int[ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  -ArcCoth[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && EqQ[b,c^2] && NeQ[m,-1]


Int[ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcTanh[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b,c^2] && EqQ[b*d-a*e,0]


Int[ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcCoth[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b,c^2] && EqQ[b*d-a*e,0]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcTanh[a+b*x]]/(1-(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Tanh[x]/b,x],x],x,ArcTanh[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sech[x]^(2*(n+1)),x],x], x, tmp]]] /;
 Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcTanh] && EqQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2,0]] /;
SimplifyFlag && QuadraticQ[v,x] && ILtQ[n,0] && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sech[x]^(2*(n+1)),x],x], x, tmp] /;
 Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcTanh] && EqQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2,0]] /;
QuadraticQ[v,x] && ILtQ[n,0] && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcCoth[a+b*x]]/(1-(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Coth[x]/b,x],x],x,ArcCoth[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*(-Csch[x]^2)^(n+1),x],x], x, tmp]]] /;
 Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcCoth] && EqQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2,0]] /;
SimplifyFlag && QuadraticQ[v,x] && ILtQ[n,0] && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*(-Csch[x]^2)^(n+1),x],x], x, tmp] /;
 Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcCoth] && EqQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2,0]] /;
QuadraticQ[v,x] && ILtQ[n,0] && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


Int[ArcTanh[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Tanh[a+b*x]] + 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,1]


Int[ArcCoth[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Tanh[a+b*x]] + 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,1]


Int[ArcTanh[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Coth[a+b*x]] + 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,1]


Int[ArcCoth[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Coth[a+b*x]] + 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,1]


Int[ArcTanh[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Tanh[a+b*x]] + 
  b*(1-c-d)*Int[x*E^(2*a+2*b*x)/(1-c+d+(1-c-d)*E^(2*a+2*b*x)),x] - 
  b*(1+c+d)*Int[x*E^(2*a+2*b*x)/(1+c-d+(1+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,1]


Int[ArcCoth[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Tanh[a+b*x]] + 
  b*(1-c-d)*Int[x*E^(2*a+2*b*x)/(1-c+d+(1-c-d)*E^(2*a+2*b*x)),x] - 
  b*(1+c+d)*Int[x*E^(2*a+2*b*x)/(1+c-d+(1+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,1]


Int[ArcTanh[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Coth[a+b*x]] + 
  b*(1+c+d)*Int[x*E^(2*a+2*b*x)/(1+c-d-(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c-d)*Int[x*E^(2*a+2*b*x)/(1-c+d-(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,1]


Int[ArcCoth[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Coth[a+b*x]] + 
  b*(1+c+d)*Int[x*E^(2*a+2*b*x)/(1+c-d-(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c-d)*Int[x*E^(2*a+2*b*x)/(1-c+d-(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcTanh[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[c+d*Tanh[a+b*x]]/(f*(m+1)) + 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcCoth[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[c+d*Tanh[a+b*x]]/(f*(m+1)) + 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcTanh[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[c+d*Coth[a+b*x]]/(f*(m+1)) + 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcCoth[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[c+d*Coth[a+b*x]]/(f*(m+1)) + 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcTanh[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[c+d*Tanh[a+b*x]]/(f*(m+1)) + 
  b*(1-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(1-c+d+(1-c-d)*E^(2*a+2*b*x)),x] - 
  b*(1+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(1+c-d+(1+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcCoth[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[c+d*Tanh[a+b*x]]/(f*(m+1)) + 
  b*(1-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(1-c+d+(1-c-d)*E^(2*a+2*b*x)),x] - 
  b*(1+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(1+c-d+(1+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcTanh[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[c+d*Coth[a+b*x]]/(f*(m+1)) + 
  b*(1+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(1+c-d-(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(1-c+d-(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcCoth[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[c+d*Coth[a+b*x]]/(f*(m+1)) + 
  b*(1+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(1+c-d-(1+c+d)*E^(2*a+2*b*x)),x] - 
  b*(1-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(1-c+d-(1-c-d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,1]


Int[ArcTanh[Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[Tan[a+b*x]] - b*Int[x*Sec[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcCoth[Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[Tan[a+b*x]] - b*Int[x*Sec[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcTanh[Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[Cot[a+b*x]] - b*Int[x*Sec[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcCoth[Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[Cot[a+b*x]] - b*Int[x*Sec[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[(e_.+f_.*x_)^m_.*ArcTanh[Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[Tan[a+b*x]]/(f*(m+1)) - b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sec[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*ArcCoth[Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[Tan[a+b*x]]/(f*(m+1)) - b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sec[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*ArcTanh[Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[Cot[a+b*x]]/(f*(m+1)) - b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sec[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*ArcCoth[Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[Cot[a+b*x]]/(f*(m+1)) - b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sec[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m,0]


Int[ArcTanh[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Tan[a+b*x]] + 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c+I*d)^2,1]


Int[ArcCoth[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Tan[a+b*x]] + 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c+I*d)^2,1]


Int[ArcTanh[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Cot[a+b*x]] + 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-I*d)^2,1]


Int[ArcCoth[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Cot[a+b*x]] + 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-I*d)^2,1]


Int[ArcTanh[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Tan[a+b*x]] + 
  I*b*(1-c+I*d)*Int[x*E^(2*I*a+2*I*b*x)/(1-c-I*d+(1-c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1+c-I*d)*Int[x*E^(2*I*a+2*I*b*x)/(1+c+I*d+(1+c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2,1]


Int[ArcCoth[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Tan[a+b*x]] + 
  I*b*(1-c+I*d)*Int[x*E^(2*I*a+2*I*b*x)/(1-c-I*d+(1-c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1+c-I*d)*Int[x*E^(2*I*a+2*I*b*x)/(1+c+I*d+(1+c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2,1]


Int[ArcTanh[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTanh[c+d*Cot[a+b*x]] - 
  I*b*(1-c-I*d)*Int[x*E^(2*I*a+2*I*b*x)/(1-c+I*d-(1-c-I*d)*E^(2*I*a+2*I*b*x)),x] + 
  I*b*(1+c+I*d)*Int[x*E^(2*I*a+2*I*b*x)/(1+c-I*d-(1+c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-I*d)^2,1]


Int[ArcCoth[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCoth[c+d*Cot[a+b*x]] - 
  I*b*(1-c-I*d)*Int[x*E^(2*I*a+2*I*b*x)/(1-c+I*d-(1-c-I*d)*E^(2*I*a+2*I*b*x)),x] + 
  I*b*(1+c+I*d)*Int[x*E^(2*I*a+2*I*b*x)/(1+c-I*d-(1+c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-I*d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcTanh[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[c+d*Tan[a+b*x]]/(f*(m+1)) + 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c+I*d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcCoth[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[c+d*Tan[a+b*x]]/(f*(m+1)) + 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c+I*d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcTanh[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[c+d*Cot[a+b*x]]/(f*(m+1)) + 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-I*d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcCoth[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[c+d*Cot[a+b*x]]/(f*(m+1)) + 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-I*d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcTanh[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[c+d*Tan[a+b*x]]/(f*(m+1)) + 
  I*b*(1-c+I*d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-c-I*d+(1-c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1+c-I*d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+c+I*d+(1+c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c+I*d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcCoth[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[c+d*Tan[a+b*x]]/(f*(m+1)) + 
  I*b*(1-c+I*d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-c-I*d+(1-c+I*d)*E^(2*I*a+2*I*b*x)),x] - 
  I*b*(1+c-I*d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+c+I*d+(1+c-I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c+I*d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcTanh[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTanh[c+d*Cot[a+b*x]]/(f*(m+1)) - 
  I*b*(1-c-I*d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-c+I*d-(1-c-I*d)*E^(2*I*a+2*I*b*x)),x] + 
  I*b*(1+c+I*d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+c-I*d-(1+c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-I*d)^2,1]


Int[(e_.+f_.*x_)^m_.*ArcCoth[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCoth[c+d*Cot[a+b*x]]/(f*(m+1)) - 
  I*b*(1-c-I*d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-c+I*d-(1-c-I*d)*E^(2*I*a+2*I*b*x)),x] + 
  I*b*(1+c+I*d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+c-I*d-(1+c+I*d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-I*d)^2,1]


Int[ArcTanh[u_],x_Symbol] :=
  x*ArcTanh[u] - 
  Int[SimplifyIntegrand[x*D[u,x]/(1-u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[ArcCoth[u_],x_Symbol] :=
  x*ArcCoth[u] - 
  Int[SimplifyIntegrand[x*D[u,x]/(1-u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcTanh[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcTanh[u])/(d*(m+1)) - 
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1-u^2),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCoth[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCoth[u])/(d*(m+1)) - 
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1-u^2),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[v_*(a_.+b_.*ArcTanh[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcTanh[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/(1-u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcTanh[u]),x]]


Int[v_*(a_.+b_.*ArcCoth[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCoth[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/(1-u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcCoth[u]),x]]





(* ::Subsection::Closed:: *)
(*7.3.1 u (a+b arcsech(c x))^n*)


Int[ArcSech[c_.*x_],x_Symbol] :=
  x*ArcSech[c*x] + Sqrt[1+c*x]*Sqrt[1/(1+c*x)]*Int[1/Sqrt[1-c^2*x^2],x] /;
FreeQ[c,x]


Int[ArcCsch[c_.*x_],x_Symbol] :=
  x*ArcCsch[c*x] + 1/c*Int[1/(x*Sqrt[1+1/(c^2*x^2)]),x] /;
FreeQ[c,x]


Int[(a_.+b_.*ArcSech[c_.*x_])^n_,x_Symbol] :=
  -1/c*Subst[Int[(a+b*x)^n*Sech[x]*Tanh[x],x],x,ArcSech[c*x]] /;
FreeQ[{a,b,c,n},x] && IGtQ[n,0]


Int[(a_.+b_.*ArcCsch[c_.*x_])^n_,x_Symbol] :=
  -1/c*Subst[Int[(a+b*x)^n*Csch[x]*Coth[x],x],x,ArcCsch[c*x]] /;
FreeQ[{a,b,c,n},x] && IGtQ[n,0]


Int[(a_.+b_.*ArcSech[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcCosh[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcCsch[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcSinh[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcSech[c*x])/(d*(m+1)) + 
  b*Sqrt[1+c*x]/(m+1)*Sqrt[1/(1+c*x)]*Int[(d*x)^m/(Sqrt[1-c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCsch[c*x])/(d*(m+1)) + 
  b*d/(c*(m+1))*Int[(d*x)^(m-1)/Sqrt[1+1/(c^2*x^2)],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[x_^m_.*(a_.+b_.*ArcSech[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Sech[x]^(m+1)*Tanh[x],x],x,ArcSech[c*x]] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && IntegerQ[m] && (GtQ[n,0] || LtQ[m,-1])


Int[x_^m_.*(a_.+b_.*ArcCsch[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Csch[x]^(m+1)*Coth[x],x],x,ArcCsch[c*x]] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && IntegerQ[m] && (GtQ[n,0] || LtQ[m,-1])


Int[(a_.+b_.*ArcSech[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  (a+b*ArcSech[c*x])*Log[1+(e-Sqrt[-c^2*d^2+e^2])/(c*d*E^ArcSech[c*x])]/e + 
  (a+b*ArcSech[c*x])*Log[1+(e+Sqrt[-c^2*d^2+e^2])/(c*d*E^ArcSech[c*x])]/e - 
  (a+b*ArcSech[c*x])*Log[1+1/E^(2*ArcSech[c*x])]/e + 
  b/e*Int[(Sqrt[(1-c*x)/(1+c*x)]*Log[1+(e-Sqrt[-c^2*d^2+e^2])/(c*d*E^ArcSech[c*x])])/(x*(1-c*x)),x] + 
  b/e*Int[(Sqrt[(1-c*x)/(1+c*x)]*Log[1+(e+Sqrt[-c^2*d^2+e^2])/(c*d*E^ArcSech[c*x])])/(x*(1-c*x)),x] - 
  b/e*Int[(Sqrt[(1-c*x)/(1+c*x)]*Log[1+1/E^(2*ArcSech[c*x])])/(x*(1-c*x)),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(a_.+b_.*ArcCsch[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  (a+b*ArcCsch[c*x])*Log[1-(e-Sqrt[c^2*d^2+e^2])*E^ArcCsch[c*x]/(c*d)]/e + 
  (a+b*ArcCsch[c*x])*Log[1-(e+Sqrt[c^2*d^2+e^2])*E^ArcCsch[c*x]/(c*d)]/e - 
  (a+b*ArcCsch[c*x])*Log[1-E^(2*ArcCsch[c*x])]/e + 
  b/(c*e)*Int[Log[1-(e-Sqrt[c^2*d^2+e^2])*E^ArcCsch[c*x]/(c*d)]/(x^2*Sqrt[1+1/(c^2*x^2)]),x] + 
  b/(c*e)*Int[Log[1-(e+Sqrt[c^2*d^2+e^2])*E^ArcCsch[c*x]/(c*d)]/(x^2*Sqrt[1+1/(c^2*x^2)]),x] - 
  b/(c*e)*Int[Log[1-E^(2*ArcCsch[c*x])]/(x^2*Sqrt[1+1/(c^2*x^2)]),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcSech[c*x])/(e*(m+1)) + 
  b*Sqrt[1+c*x]/(e*(m+1))*Sqrt[1/(1+c*x)]*Int[(d+e*x)^(m+1)/(x*Sqrt[1-c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCsch[c*x])/(e*(m+1)) + 
  b/(c*e*(m+1))*Int[(d+e*x)^(m+1)/(x^2*Sqrt[1+1/(c^2*x^2)]),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1] && IntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCsch[c*x])/(e*(m+1)) -
  b*c*x/(e*(m+1)*Sqrt[-c^2*x^2])*Int[(d+e*x)^(m+1)/(x*Sqrt[-1-c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e,m},x] && Not[IntegerQ[m]]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcSech[c*x]),u,x] + b*Sqrt[1+c*x]*Sqrt[1/(1+c*x)]*Int[SimplifyIntegrand[u/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcCsch[c*x]),u,x] - b*c*x/Sqrt[-c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[-1-c^2*x^2]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[e-c^2*d,0] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[e-c^2*d,0] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSech[c*x])/(2*e*(p+1)) + 
  b*Sqrt[1+c*x]/(2*e*(p+1))*Sqrt[1/(1+c*x)]*Int[(d+e*x^2)^(p+1)/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCsch[c*x])/(2*e*(p+1)) - 
  b*c*x/(2*e*(p+1)*Sqrt[-c^2*x^2])*Int[(d+e*x^2)^(p+1)/(x*Sqrt[-1-c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcSech[c*x]),u,x] + b*Sqrt[1+c*x]*Sqrt[1/(1+c*x)]*Int[SimplifyIntegrand[u/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && (
  IGtQ[p,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*p+3,0]] || 
  IGtQ[(m+1)/2,0] && Not[ILtQ[p,0] && GtQ[m+2*p+3,0]] || 
  ILtQ[(m+2*p+1)/2,0] && Not[ILtQ[(m-1)/2,0]])


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcCsch[c*x]),u,x] - b*c*x/Sqrt[-c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[-1-c^2*x^2]),x],x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && (
  IGtQ[p,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*p+3,0]] || 
  IGtQ[(m+1)/2,0] && Not[ILtQ[p,0] && GtQ[m+2*p+3,0]] || 
  ILtQ[(m+2*p+1)/2,0] && Not[ILtQ[(m-1)/2,0]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegersQ[m,p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegersQ[m,p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[e-c^2*d,0] && IntegerQ[m] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[e-c^2*d,0] && IntegerQ[m] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]


Int[u_*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[(a+b*ArcSech[c*x]),v,x] + 
  b*Sqrt[1-c^2*x^2]/(c*x*Sqrt[-1+1/(c*x)]*Sqrt[1+1/(c*x)])*
    Int[SimplifyIntegrand[v/(x*Sqrt[1-c^2*x^2]),x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[u_*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[(a+b*ArcCsch[c*x]),v,x] - 
  b*c*x/Sqrt[-c^2*x^2]*Int[SimplifyIntegrand[v/(x*Sqrt[-1-c^2*x^2]),x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[u_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcSech[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcCsch[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*7.3.2 Miscellaneous inverse hyperbolic secant*)


Int[ArcSech[c_+d_.*x_],x_Symbol] :=
  (c+d*x)*ArcSech[c+d*x]/d + 
  Int[Sqrt[(1-c-d*x)/(1+c+d*x)]/(1-c-d*x),x] /;
FreeQ[{c,d},x]


Int[ArcCsch[c_+d_.*x_],x_Symbol] :=
  (c+d*x)*ArcCsch[c+d*x]/d + 
  Int[1/((c+d*x)*Sqrt[1+1/(c+d*x)^2]),x] /;
FreeQ[{c,d},x]


Int[(a_.+b_.*ArcSech[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcSech[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcCsch[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCsch[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcSech[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(a+b*ArcSech[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]


Int[(a_.+b_.*ArcCsch[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(a+b*ArcCsch[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSech[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(f*x/d)^m*(a+b*ArcSech[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsch[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(f*x/d)^m*(a+b*ArcCsch[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]


(* Int[x_^m_.*ArcSech[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcSech[a+b*x]/(b^(m+1)*(m+1)) + 
  1/(b^(m+1)*(m+1))*Subst[Int[((-a*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[-1+x]*Sqrt[1+x]),x],x,1/(a+b*x)] /;
FreeQ[{a,b},x] && IntegerQ[m] && NeQ[m,-1] *)


(* Int[x_^m_.*ArcCsch[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcCsch[a+b*x]/(b^(m+1)*(m+1)) + 
  1/(b^(m+1)*(m+1))*Subst[Int[((-a*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1+x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b},x] && IntegerQ[m] && NeQ[m,-1] *)


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSech[c_+d_.*x_])^p_.,x_Symbol] :=
  -1/d^(m+1)*Subst[Int[(a+b*x)^p*Sech[x]*Tanh[x]*(d*e-c*f+f*Sech[x])^m,x],x,ArcSech[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsch[c_+d_.*x_])^p_.,x_Symbol] :=
  -1/d^(m+1)*Subst[Int[(a+b*x)^p*Csch[x]*Coth[x]*(d*e-c*f+f*Csch[x])^m,x],x,ArcCsch[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSech[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSech[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsch[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCsch[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSech[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(e+f*x)^m*(a+b*ArcSech[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsch[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(e+f*x)^m*(a+b*ArcCsch[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]


Int[u_.*ArcSech[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCosh[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCsch[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSinh[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[E^ArcSech[a_.*x_], x_Symbol] :=
  x*E^ArcSech[a*x] + Log[x]/a + 1/a*Int[1/(x*(1-a*x))*Sqrt[(1-a*x)/(1+a*x)],x] /;
FreeQ[a,x]


Int[E^ArcSech[a_.*x_^p_], x_Symbol] :=
  x*E^ArcSech[a*x^p] + 
  p/a*Int[1/x^p,x] + 
  p*Sqrt[1+a*x^p]/a*Sqrt[1/(1+a*x^p)]*Int[1/(x^p*Sqrt[1+a*x^p]*Sqrt[1-a*x^p]),x] /;
FreeQ[{a,p},x]


Int[E^ArcCsch[a_.*x_^p_.], x_Symbol] :=
  1/a*Int[1/x^p,x] + Int[Sqrt[1+1/(a^2*x^(2*p))],x] /;
FreeQ[{a,p},x]


Int[E^(n_.*ArcSech[u_]), x_Symbol] :=
  Int[(1/u + Sqrt[(1-u)/(1+u)] + 1/u*Sqrt[(1-u)/(1+u)])^n,x] /;
IntegerQ[n]


Int[E^(n_.*ArcCsch[u_]), x_Symbol] :=
  Int[(1/u + Sqrt[1+1/u^2])^n,x] /;
IntegerQ[n]


Int[E^ArcSech[a_.*x_^p_.]/x_, x_Symbol] :=
  -1/(a*p*x^p) + 
  Sqrt[1+a*x^p]/a*Sqrt[1/(1+a*x^p)]*Int[Sqrt[1+a*x^p]*Sqrt[1-a*x^p]/x^(p+1),x] /;
FreeQ[{a,p},x]


Int[x_^m_.*E^ArcSech[a_.*x_^p_.], x_Symbol] :=
  x^(m+1)*E^ArcSech[a*x^p]/(m+1) + 
  p/(a*(m+1))*Int[x^(m-p),x] + 
  p*Sqrt[1+a*x^p]/(a*(m+1))*Sqrt[1/(1+a*x^p)]*Int[x^(m-p)/(Sqrt[1+a*x^p]*Sqrt[1-a*x^p]),x] /;
FreeQ[{a,m,p},x] && NeQ[m,-1]


Int[x_^m_.*E^ArcCsch[a_.*x_^p_.], x_Symbol] :=
  1/a*Int[x^(m-p),x] + Int[x^m*Sqrt[1+1/(a^2*x^(2*p))],x] /;
FreeQ[{a,m,p},x]


Int[x_^m_.*E^(n_.*ArcSech[u_]), x_Symbol] :=
  Int[x^m*(1/u + Sqrt[(1-u)/(1+u)] + 1/u*Sqrt[(1-u)/(1+u)])^n,x] /;
FreeQ[m,x] && IntegerQ[n]


Int[x_^m_.*E^(n_.*ArcCsch[u_]), x_Symbol] :=
  Int[x^m*(1/u + Sqrt[1+1/u^2])^n,x] /;
FreeQ[m,x] && IntegerQ[n]


Int[E^(ArcSech[c_.*x_])/(a_+b_.*x_^2), x_Symbol] :=
  1/(a*c)*Int[Sqrt[1/(1+c*x)]/(x*Sqrt[1-c*x]),x] + 1/c*Int[1/(x*(a+b*x^2)),x] /;
FreeQ[{a,b,c},x] && EqQ[b+a*c^2,0]


Int[E^(ArcCsch[c_.*x_])/(a_+b_.*x_^2), x_Symbol] :=
  1/(a*c^2)*Int[1/(x^2*Sqrt[1+1/(c^2*x^2)]),x] + 1/c*Int[1/(x*(a+b*x^2)),x] /;
FreeQ[{a,b,c},x] && EqQ[b-a*c^2,0]


Int[(d_.*x_)^m_.*E^(ArcSech[c_.*x_])/(a_+b_.*x_^2), x_Symbol] :=
  d/(a*c)*Int[(d*x)^(m-1)*Sqrt[1/(1+c*x)]/Sqrt[1-c*x],x] + d/c*Int[(d*x)^(m-1)/(a+b*x^2),x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[b+a*c^2,0]


Int[(d_.*x_)^m_.*E^(ArcCsch[c_.*x_])/(a_+b_.*x_^2), x_Symbol] :=
  d^2/(a*c^2)*Int[(d*x)^(m-2)/Sqrt[1+1/(c^2*x^2)],x] + d/c*Int[(d*x)^(m-1)/(a+b*x^2),x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[b-a*c^2,0]


Int[ArcSech[u_],x_Symbol] :=
  x*ArcSech[u] +
  Sqrt[1-u^2]/(u*Sqrt[-1+1/u]*Sqrt[1+1/u])*Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[1-u^2]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCsch[u_],x_Symbol] :=
  x*ArcCsch[u] -
  u/Sqrt[-u^2]*Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[-1-u^2]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSech[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcSech[u])/(d*(m+1)) + 
  b*Sqrt[1-u^2]/(d*(m+1)*u*Sqrt[-1+1/u]*Sqrt[1+1/u])*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[1-u^2]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCsch[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCsch[u])/(d*(m+1)) - 
  b*u/(d*(m+1)*Sqrt[-u^2])*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[-1-u^2]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSech[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcSech[u]),w,x] + b*Sqrt[1-u^2]/(u*Sqrt[-1+1/u]*Sqrt[1+1/u])*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[1-u^2]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCsch[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCsch[u]),w,x] - b*u/Sqrt[-u^2]*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[-1-u^2]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]



