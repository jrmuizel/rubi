(* ::Package:: *)

(* ::Section:: *)
(*Inverse Trig Function Rules*)


(* ::Subsection::Closed:: *)
(*5.1.1 (a+b arcsin(c x))^n*)


Int[(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcSin[c*x])^n - 
  b*c*n*Int[x*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && GtQ[n,0]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcCos[c*x])^n + 
  b*c*n*Int[x*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && GtQ[n,0]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) + 
  c/(b*(n+1))*Int[x*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && LtQ[n,-1]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  c/(b*(n+1))*Int[x*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && LtQ[n,-1]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  1/(b*c)*Subst[Int[x^n*Cos[a/b-x/b],x],x,a+b*ArcSin[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  1/(b*c)*Subst[Int[x^n*Sin[a/b-x/b],x],x,a+b*ArcCos[c*x]] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*5.1.2 (d x)^m (a+b arcsin(c x))^n*)


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./x_,x_Symbol] :=
  Subst[Int[(a+b*x)^n/Tan[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c},x] && IGtQ[n,0]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./x_,x_Symbol] :=
  -Subst[Int[(a+b*x)^n/Cot[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c},x] && IGtQ[n,0]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcSin[c*x])^n/(d*(m+1)) - 
  b*c*n/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCos[c*x])^n/(d*(m+1)) + 
  b*c*n/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && NeQ[m,-1]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcSin[c*x])^n/(m+1) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && GtQ[n,0]


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcCos[c*x])^n/(m+1) + 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && GtQ[n,0]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1),Sin[x]^(m-1)*(m-(m+1)*Sin[x]^2),x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && GeQ[n,-2] && LtQ[n,-1]


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -x^m*Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1),Cos[x]^(m-1)*(m-(m+1)*Cos[x]^2),x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && GeQ[n,-2] && LtQ[n,-1]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] + 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && LtQ[n,-2]


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -x^m*Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] - 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && IGtQ[m,0] && LtQ[n,-2]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]^m*Cos[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,n},x] && IGtQ[m,0]


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]^m*Sin[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,n},x] && IGtQ[m,0]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d*x)^m*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d*x)^m*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]





(* ::Subsection::Closed:: *)
(*5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n*)


(* Int[(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c*Sqrt[d])*Subst[Int[(a+b*x)^n,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && GtQ[d,0] *)


(* Int[(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(c*Sqrt[d])*Subst[Int[(a+b*x)^n,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && GtQ[d,0] *)


Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])),x_Symbol] :=
  Log[a+b*ArcSin[c*x]]/(b*c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[d,0]


Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])),x_Symbol] :=
  -Log[a+b*ArcCos[c*x]]/(b*c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[d,0]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && NeQ[n,-1]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && NeQ[n,-1]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && Not[GtQ[d,0]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^p/(2*p+1)*Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^p/(2*p+1)*Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && (IntegerQ[p] || GtQ[d,0]) *)


Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/2 - 
  b*c*n*Sqrt[d+e*x^2]/(2*Sqrt[1-c^2*x^2])*Int[x*(a+b*ArcSin[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/(2*Sqrt[1-c^2*x^2])*Int[(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]


Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/2 + 
  b*c*n*Sqrt[d+e*x^2]/(2*Sqrt[1-c^2*x^2])*Int[x*(a+b*ArcCos[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/(2*Sqrt[1-c^2*x^2])*Int[(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/((2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/((2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcSin[c*x])^n/(d*Sqrt[d+e*x^2]) - 
  b*c*n/Sqrt[d]*Int[x*(a+b*ArcSin[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[d,0]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcCos[c*x])^n/(d*Sqrt[d+e*x^2]) + 
  b*c*n/Sqrt[d]*Int[x*(a+b*ArcCos[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[d,0]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcSin[c*x])^n/(d*Sqrt[d+e*x^2]) - 
  b*c*n*Sqrt[1-c^2*x^2]/(d*Sqrt[d+e*x^2])*Int[x*(a+b*ArcSin[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcCos[c*x])^n/(d*Sqrt[d+e*x^2]) + 
  b*c*n*Sqrt[1-c^2*x^2]/(d*Sqrt[d+e*x^2])*Int[x*(a+b*ArcCos[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]


(* Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*c*n*d^p/(2*(p+1))*Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*c*n*d^p/(2*(p+1))*Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/(c*d)*Subst[Int[(a+b*x)^n*Sec[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -1/(c*d)*Subst[Int[(a+b*x)^n*Csc[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  d^p*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) + 
  c*d^p*(2*p+1)/(b*(n+1))*Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -d^p*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  c*d^p*(2*p+1)/(b*(n+1))*Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) + 
  c*(2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  c*(2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*(n+1)*(1-c^2*x^2)^FracPart[p])*
     Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^p/c*Subst[Int[(a+b*x)^n*Cos[x]^(2*p+1),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p,0] && (IntegerQ[p] || GtQ[d,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c*Subst[Int[(a+b*x)^n*Sin[x]^(2*p+1),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p,0] && (IntegerQ[p] || GtQ[d,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p,0] && Not[IntegerQ[p] || GtQ[d,0]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p,0] && Not[IntegerQ[p] || GtQ[d,0]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d+e,0] && (IGtQ[p,0] || ILtQ[p+1/2,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d+e,0] && (IGtQ[p,0] || ILtQ[p+1/2,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n,(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[n,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n,(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[n,0])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (-d^2*g/e)^q*Int[(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (-d^2*g/e)^q*Int[(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^q*(f+g*x)^q/(1-c^2*x^2)^q*Int[(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^q*(f+g*x)^q/(1-c^2*x^2)^q*Int[(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]





(* ::Subsection::Closed:: *)
(*5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n*)


Int[x_*(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -1/e*Subst[Int[(a+b*x)^n*Tan[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


Int[x_*(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Subst[Int[(a+b*x)^n*Cot[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


(* Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) + 
  b*n*d^p/(2*c*(p+1))*Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && NeQ[p,-1] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  b*n*d^p/(2*c*(p+1))*Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && NeQ[p,-1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) + 
  b*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && NeQ[p,-1]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  b*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && NeQ[p,-1]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  1/d*Subst[Int[(a+b*x)^n/(Cos[x]*Sin[x]),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  -1/d*Subst[Int[(a+b*x)^n/(Cos[x]*Sin[x]),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) + 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])/x_,x_Symbol] :=
  (d+e*x^2)^p*(a+b*ArcSin[c*x])/(2*p) - 
  b*c*d^p/(2*p)*Int[(1-c^2*x^2)^(p-1/2),x] + 
  d*Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])/x,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])/x_,x_Symbol] :=
  (d+e*x^2)^p*(a+b*ArcCos[c*x])/(2*p) + 
  b*c*d^p/(2*p)*Int[(1-c^2*x^2)^(p-1/2),x] + 
  d*Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])/x,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])/(f*(m+1)) - 
  b*c*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2),x] - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && ILtQ[(m+1)/2,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])/(f*(m+1)) + 
  b*c*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2),x] - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && ILtQ[(m+1)/2,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1-c^2*x^2)^p,x]},  
  Dist[d^p*(a+b*ArcSin[c*x]),u,x] - b*c*d^p*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0]) && 
  NeQ[p,-1/2] && GtQ[d,0]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1-c^2*x^2)^p,x]},  
  Dist[d^p*(a+b*ArcCos[c*x]),u,x] + b*c*d^p*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0]) && 
  NeQ[p,-1/2] && GtQ[d,0]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1-c^2*x^2)^p,x]},
  (a+b*ArcSin[c*x])*Int[x^m*(d+e*x^2)^p,x] - 
  b*c*d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1-c^2*x^2)^p,x]},
  (a+b*ArcCos[c*x])*Int[x^m*(d+e*x^2)^p,x] + 
  b*c*d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(f*(m+1)) - 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+1)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1),x] + 
  c^2*Sqrt[d+e*x^2]/(f^2*(m+1)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+2)*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(f*(m+1)) + 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+1)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1),x] + 
  c^2*Sqrt[d+e*x^2]/(f^2*(m+1)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+2)*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+2*p+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]] && 
  (IntegerQ[p] || GtQ[d,0]) && (RationalQ[m] || EqQ[n,1]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^p/(f*(m+2*p+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]] && 
  (IntegerQ[p] || GtQ[d,0]) && (RationalQ[m] || EqQ[n,1]) *)


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(f*(m+2)) - 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+2)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/((m+2)*Sqrt[1-c^2*x^2])*Int[(f*x)^m*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && Not[LtQ[m,-1]] && (RationalQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(f*(m+2)) + 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+2)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/((m+2)*Sqrt[1-c^2*x^2])*Int[(f*x)^m*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && Not[LtQ[m,-1]] && (RationalQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]] && (RationalQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]] && (RationalQ[m] || EqQ[n,1])


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1] && IntegerQ[m]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*f*n*d^p/(2*c*(p+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && GtQ[m,1] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*f*n*d^p/(2*c*(p+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && GtQ[m,1] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && GtQ[m,1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && GtQ[m,1]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*c*n*d^p/(2*f*(p+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[p] || GtQ[d,0]) && 
  (IntegerQ[m] || IntegerQ[p] || EqQ[n,1]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*c*n*d^p/(2*f*(p+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[p] || GtQ[d,0]) && 
  (IntegerQ[m] || IntegerQ[p] || EqQ[n,1]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*f*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[m] || IntegerQ[p] || EqQ[n,1])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*f*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[m] || IntegerQ[p] || EqQ[n,1])


(* Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(e*m) + 
  b*f*n/(c*m*Sqrt[d])*Int[(f*x)^(m-1)*(a+b*ArcSin[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcSin[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && GtQ[d,0] && IntegerQ[m] *)


(* Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(e*m) - 
  b*f*n*Sqrt[1-c^2*x^2]/(c*m*Sqrt[d+e*x^2])*Int[(f*x)^(m-1)*(a+b*ArcCos[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcCos[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && GtQ[d,0] && IntegerQ[m] *)


Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(e*m) + 
  b*f*n*Sqrt[1-c^2*x^2]/(c*m*Sqrt[d+e*x^2])*Int[(f*x)^(m-1)*(a+b*ArcSin[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcSin[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && IntegerQ[m]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(e*m) - 
  b*f*n*Sqrt[1-c^2*x^2]/(c*m*Sqrt[d+e*x^2])*Int[(f*x)^(m-1)*(a+b*ArcCos[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcCos[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && IntegerQ[m]


Int[x_^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*Sin[x]^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && IGtQ[n,0] && IntegerQ[m]


Int[x_^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*Cos[x]^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && IGtQ[n,0] && IntegerQ[m]


Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*(a+b*ArcSin[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2]/(Sqrt[d]*f*(m+1)) - 
  b*c*(f*x)^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2]/(Sqrt[d]*f^2*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*(a+b*ArcCos[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2]/(Sqrt[d]*f*(m+1)) + 
  b*c*(f*x)^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2]/(Sqrt[d]*f^2*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(f*x)^m*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && Not[GtQ[d,0]] && (IntegerQ[m] || EqQ[n,1])


Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(f*x)^m*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && Not[GtQ[d,0]] && (IntegerQ[m] || EqQ[n,1])


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] + 
  b*f*n*d^p/(c*(m+2*p+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && (IntegerQ[p] || GtQ[d,0]) && IntegerQ[m] *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] - 
  b*f*n*d^p/(c*(m+2*p+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && (IntegerQ[p] || GtQ[d,0]) && IntegerQ[m] *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] + 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(c*(m+2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] - 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(c*(m+2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[m]


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && EqQ[m+2*p+1,0] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && EqQ[m+2*p+1,0] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && EqQ[m+2*p+1,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && EqQ[m+2*p+1,0]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^m*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  f*m/(b*c*Sqrt[d]*(n+1))*Int[(f*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && GtQ[d,0]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -(f*x)^m*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  f*m/(b*c*Sqrt[d]*(n+1))*Int[(f*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && GtQ[d,0]


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] + 
  c*(m+2*p+1)*d^p/(b*f*(n+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IGtQ[m,-3] && IGtQ[2*p,0] && (IntegerQ[p] || GtQ[d,0]) *)


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] - 
  c*(m+2*p+1)*d^p/(b*f*(n+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IGtQ[m,-3] && IGtQ[2*p,0] && (IntegerQ[p] || GtQ[d,0]) *)


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] + 
  c*(m+2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*f*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IGtQ[m,-3] && IGtQ[2*p,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] - 
  c*(m+2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*f*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IGtQ[m,-3] && IGtQ[2*p,0]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]^m*Cos[x]^(2*p+1),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IntegerQ[2*p] && GtQ[p,-1] && IGtQ[m,0] && (IntegerQ[p] || GtQ[d,0])


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]^m*Sin[x]^(2*p+1),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IntegerQ[2*p] && GtQ[p,-1] && IGtQ[m,0] && (IntegerQ[p] || GtQ[d,0])


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IntegerQ[2*p] && GtQ[p,-1] && IGtQ[m,0] && Not[(IntegerQ[p] || GtQ[d,0])]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IntegerQ[2*p] && GtQ[p,-1] && IGtQ[m,0] && Not[(IntegerQ[p] || GtQ[d,0])]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] && (EqQ[m,-1] || EqQ[m,-2])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] && (EqQ[m,-1] || EqQ[m,-2])


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])/(2*e*(p+1)) - b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[c^2*d+e,0] && NeQ[p,-1]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])/(2*e*(p+1)) + b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[c^2*d+e,0] && NeQ[p,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[(m-1)/2,0] && LeQ[m+p,0])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[(m-1)/2,0] && LeQ[m+p,0])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[c^2*d+e,0] && IGtQ[n,0] && IntegerQ[p] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[c^2*d+e,0] && IGtQ[n,0] && IntegerQ[p] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (-d^2*g/e)^q*Int[(h*x)^m*(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]


Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (-d^2*g/e)^q*Int[(h*x)^m*(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]


Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (-d^2*g/e)^IntPart[q]*(d+e*x)^FracPart[q]*(f+g*x)^FracPart[q]/(1-c^2*x^2)^FracPart[q]*
    Int[(h*x)^m*(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]


Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (-d^2*g/e)^IntPart[q]*(d+e*x)^FracPart[q]*(f+g*x)^FracPart[q]/(1-c^2*x^2)^FracPart[q]*
    Int[(h*x)^m*(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]





(* ::Subsection::Closed:: *)
(*5.1.5 u (a+b arcsin(c x))^n*)


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  Subst[Int[(a+b*x)^n*Cos[x]/(c*d+e*Sin[x]),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[n,0]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  -Subst[Int[(a+b*x)^n*Sin[x]/(c*d+e*Cos[x]),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[n,0]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcSin[c*x])^n/(e*(m+1)) - 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,0] && NeQ[m,-1]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCos[c*x])^n/(e*(m+1)) + 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,0] && NeQ[m,-1]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[m,0] && LtQ[n,-1]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[m,0] && LtQ[n,-1]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]*(c*d+e*Sin[x])^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[m,0]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]*(c*d+e*Cos[x])^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[m,0]


Int[Px_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[ExpandExpression[Px,x],x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x]


Int[Px_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[ExpandExpression[Px,x],x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x]


(* Int[Px_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  With[{u=IntHide[Px,x]},  
  Dist[(a+b*ArcSin[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x] && IGtQ[n,0] *)


(* Int[Px_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  With[{u=IntHide[Px,x]},  
  Dist[(a+b*ArcCos[c*x])^n,u,x] + b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x] && IGtQ[n,0] *)


Int[Px_*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]


Int[Px_*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]


Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[Px*(d+e*x)^m,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]


Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[Px*(d+e*x)^m,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]


Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},  
  Dist[(a+b*ArcSin[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[m,0] && LtQ[m+p+1,0]


Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},  
  Dist[(a+b*ArcCos[c*x])^n,u,x] + b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[m,0] && LtQ[m+p+1,0]


Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
  With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},  
  Dist[(a+b*ArcSin[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[n,0] && IGtQ[p,0] && EqQ[e*g-2*d*h,0]


Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
  With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},  
  Dist[(a+b*ArcCos[c*x])^n,u,x] + b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[n,0] && IGtQ[p,0] && EqQ[e*g-2*d*h,0]


Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && IGtQ[n,0] && IntegerQ[m]


Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && IGtQ[n,0] && IntegerQ[m]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f+g*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && ILtQ[p+1/2,0] && GtQ[d,0] && (LtQ[m,-2*p-1] || GtQ[m,3])


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f+g*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && ILtQ[p+1/2,0] && GtQ[d,0] && (LtQ[m,-2*p-1] || GtQ[m,3])


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && IntegerQ[p+1/2] && GtQ[d,0] && IGtQ[n,0] && 
  (m==1 || p>0 || n==1 && p>-1 || m==2 && p<-2)


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && IntegerQ[p+1/2] && GtQ[d,0] && IGtQ[n,0] && 
  (m==1 || p>0 || n==1 && p>-1 || m==2 && p<-2)


Int[(f_+g_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f+g*x)^m*(d+e*x^2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  1/(b*c*Sqrt[d]*(n+1))*Int[(d*g*m+2*e*f*x+e*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && ILtQ[m,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -(f+g*x)^m*(d+e*x^2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  1/(b*c*Sqrt[d]*(n+1))*Int[(d*g*m+2*e*f*x+e*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && ILtQ[m,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n,(f+g*x)^m*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IGtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n,(f+g*x)^m*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IGtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f+g*x)^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  1/(b*c*Sqrt[d]*(n+1))*
    Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),(d*g*m+e*f*(2*p+1)*x+e*g*(m+2*p+1)*x^2)*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && ILtQ[m,0] && IGtQ[p-1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -(f+g*x)^m*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  1/(b*c*Sqrt[d]*(n+1))*
    Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),(d*g*m+e*f*(2*p+1)*x+e*g*(m+2*p+1)*x^2)*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && ILtQ[m,0] && IGtQ[p-1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f+g*x)^m*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && GtQ[d,0] && LtQ[n,-1]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -(f+g*x)^m*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && GtQ[d,0] && LtQ[n,-1]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*(c*f+g*Sin[x])^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && GtQ[d,0] && (GtQ[m,0] || IGtQ[n,0])


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*(c*f+g*Cos[x])^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && GtQ[d,0] && (GtQ[m,0] || IGtQ[n,0])


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n/Sqrt[d+e*x^2],(f+g*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && ILtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n/Sqrt[d+e*x^2],(f+g*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && ILtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[(f+g*x)^m*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p-1/2] && Not[GtQ[d,0]]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[(f+g*x)^m*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p-1/2] && Not[GtQ[d,0]]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Log[h*(f+g*x)^m]*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(a+b*ArcSin[c*x])^(n+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && IGtQ[n,0]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -Log[h*(f+g*x)^m]*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(a+b*ArcCos[c*x])^(n+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && IGtQ[n,0]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[Log[h*(f+g*x)^m]*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && Not[GtQ[d,0]]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[Log[h*(f+g*x)^m]*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && Not[GtQ[d,0]]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m+1/2,0]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m+1/2,0]


Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]


Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]


Int[u_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[a+b*ArcSin[c*x],v,x] - b*c*Int[SimplifyIntegrand[v/Sqrt[1-c^2*x^2],x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[u_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[a+b*ArcCos[c*x],v,x] + b*c*Int[SimplifyIntegrand[v/Sqrt[1-c^2*x^2],x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[Px_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]


Int[Px_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]


Int[Px_.*(f_+g_.*(d_+e_.*x_^2)^p_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(f+g*(d+e*x^2)^p)^m*(a+b*ArcSin[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && IntegersQ[m,n]


Int[Px_.*(f_+g_.*(d_+e_.*x_^2)^p_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(f+g*(d+e*x^2)^p)^m*(a+b*ArcCos[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && IntegersQ[m,n]


Int[RFx_*ArcSin[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[ArcSin[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[c,x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[RFx_*ArcCos[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[ArcCos[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[c,x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[RFx_*(a_+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[RFx*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[RFx_*(a_+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[RFx*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[RFx_*(d_+e_.*x_^2)^p_*ArcSin[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(d+e*x^2)^p*ArcSin[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]


Int[RFx_*(d_+e_.*x_^2)^p_*ArcCos[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(d+e*x^2)^p*ArcCos[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]


Int[RFx_*(d_+e_.*x_^2)^p_*(a_+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p,RFx*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]


Int[RFx_*(d_+e_.*x_^2)^p_*(a_+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p,RFx*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]


Int[u_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*5.1.6 Miscellaneous inverse sine*)
(**)


Int[(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x]


Int[(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[Sqrt[a_.+b_.*ArcSin[c_+d_.*x_^2]],x_Symbol] :=
  x*Sqrt[a+b*ArcSin[c+d*x^2]] - 
  Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelC[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Sqrt[c/b]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) + 
  Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelS[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Sqrt[c/b]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1]


Int[Sqrt[a_.+b_.*ArcCos[1+d_.*x_^2]],x_Symbol] :=
  -2*Sqrt[a+b*ArcCos[1+d*x^2]]*Sin[ArcCos[1+d*x^2]/2]^2/(d*x) - 
  2*Sqrt[Pi]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(Sqrt[1/b]*d*x) + 
  2*Sqrt[Pi]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(Sqrt[1/b]*d*x) /;
FreeQ[{a,b,d},x]


Int[Sqrt[a_.+b_.*ArcCos[-1+d_.*x_^2]],x_Symbol] :=
  2*Sqrt[a+b*ArcCos[-1+d*x^2]]*Cos[(1/2)*ArcCos[-1+d*x^2]]^2/(d*x) - 
  2*Sqrt[Pi]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(Sqrt[1/b]*d*x) - 
  2*Sqrt[Pi]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(Sqrt[1/b]*d*x) /;
FreeQ[{a,b,d},x]


Int[(a_.+b_.*ArcSin[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcSin[c+d*x^2])^n + 
  2*b*n*Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcSin[c+d*x^2])^(n-1)/(d*x) - 
  4*b^2*n*(n-1)*Int[(a+b*ArcSin[c+d*x^2])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && GtQ[n,1]


Int[(a_.+b_.*ArcCos[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcCos[c+d*x^2])^n - 
  2*b*n*Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcCos[c+d*x^2])^(n-1)/(d*x) - 
  4*b^2*n*(n-1)*Int[(a+b*ArcCos[c+d*x^2])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && GtQ[n,1]


Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2]),x_Symbol] :=
  -x*(c*Cos[a/(2*b)]-Sin[a/(2*b)])*CosIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
    (2*b*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) - 
  x*(c*Cos[a/(2*b)]+Sin[a/(2*b)])*SinIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
    (2*b*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1]


Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2]),x_Symbol] :=
  x*Cos[a/(2*b)]*CosIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[-d*x^2]) + 
  x*Sin[a/(2*b)]*SinIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[-d*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2]),x_Symbol] :=
  x*Sin[a/(2*b)]*CosIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) - 
  x*Cos[a/(2*b)]*SinIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/Sqrt[a_.+b_.*ArcSin[c_+d_.*x_^2]],x_Symbol] :=
  -Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelC[1/(Sqrt[b*c]*Sqrt[Pi])*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Sqrt[b*c]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) - 
  Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelS[(1/(Sqrt[b*c]*Sqrt[Pi]))*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Sqrt[b*c]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1]


Int[1/Sqrt[a_.+b_.*ArcCos[1+d_.*x_^2]],x_Symbol] :=
  -2*Sqrt[Pi/b]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) - 
   2*Sqrt[Pi/b]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[1/Sqrt[a_.+b_.*ArcCos[-1+d_.*x_^2]],x_Symbol] :=
  2*Sqrt[Pi/b]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) - 
  2*Sqrt[Pi/b]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2])^(3/2),x_Symbol] :=
  -Sqrt[-2*c*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcSin[c+d*x^2]]) - 
  (c/b)^(3/2)*Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelC[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Cos[(1/2)*ArcSin[c+d*x^2]]-c*Sin[ArcSin[c+d*x^2]/2]) + 
  (c/b)^(3/2)*Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelS[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Cos[(1/2)*ArcSin[c+d*x^2]]-c*Sin[ArcSin[c+d*x^2]/2]) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1]


Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2])^(3/2),x_Symbol] :=
  Sqrt[-2*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcCos[1+d*x^2]]) - 
  2*(1/b)^(3/2)*Sqrt[Pi]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) + 
  2*(1/b)^(3/2)*Sqrt[Pi]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2])^(3/2),x_Symbol] :=
  Sqrt[2*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcCos[-1+d*x^2]]) - 
  2*(1/b)^(3/2)*Sqrt[Pi]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) - 
  2*(1/b)^(3/2)*Sqrt[Pi]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2])^2,x_Symbol] :=
  -Sqrt[-2*c*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcSin[c+d*x^2])) - 
  x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*CosIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
    (4*b^2*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) + 
  x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*SinIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
    (4*b^2*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1]


Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2])^2,x_Symbol] :=
  Sqrt[-2*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcCos[1+d*x^2])) + 
  x*Sin[a/(2*b)]*CosIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[(-d)*x^2]) - 
  x*Cos[a/(2*b)]*SinIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[(-d)*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2])^2,x_Symbol] :=
  Sqrt[2*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcCos[-1+d*x^2])) - 
  x*Cos[a/(2*b)]*CosIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) - 
  x*Sin[a/(2*b)]*SinIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) /;
FreeQ[{a,b,d},x]


Int[(a_.+b_.*ArcSin[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcSin[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) + 
  Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcSin[c+d*x^2])^(n+1)/(2*b*d*(n+1)*x) - 
  1/(4*b^2*(n+1)*(n+2))*Int[(a+b*ArcSin[c+d*x^2])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && LtQ[n,-1] && NeQ[n,-2]


Int[(a_.+b_.*ArcCos[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcCos[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) - 
  Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcCos[c+d*x^2])^(n+1)/(2*b*d*(n+1)*x) - 
  1/(4*b^2*(n+1)*(n+2))*Int[(a+b*ArcCos[c+d*x^2])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && LtQ[n,-1] && NeQ[n,-2]


Int[ArcSin[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Cot[x],x],x,ArcSin[a*x^p]] /;
FreeQ[{a,p},x] && IGtQ[n,0]


Int[ArcCos[a_.*x_^p_]^n_./x_,x_Symbol] :=
  -1/p*Subst[Int[x^n*Tan[x],x],x,ArcCos[a*x^p]] /;
FreeQ[{a,p},x] && IGtQ[n,0]


Int[u_.*ArcSin[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCsc[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCos[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSec[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[ArcSin[Sqrt[1+b_.*x_^2]]^n_./Sqrt[1+b_.*x_^2],x_Symbol] :=
  Sqrt[-b*x^2]/(b*x)*Subst[Int[ArcSin[x]^n/Sqrt[1-x^2],x],x,Sqrt[1+b*x^2]] /;
FreeQ[{b,n},x]


Int[ArcCos[Sqrt[1+b_.*x_^2]]^n_./Sqrt[1+b_.*x_^2],x_Symbol] :=
  Sqrt[-b*x^2]/(b*x)*Subst[Int[ArcCos[x]^n/Sqrt[1-x^2],x],x,Sqrt[1+b*x^2]] /;
FreeQ[{b,n},x]


Int[u_.*f_^(c_.*ArcSin[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[ReplaceAll[u,x->-a/b+Sin[x]/b]*f^(c*x^n)*Cos[x],x],x,ArcSin[a+b*x]] /;
FreeQ[{a,b,c,f},x] && IGtQ[n,0]


Int[u_.*f_^(c_.*ArcCos[a_.+b_.*x_]^n_.),x_Symbol] :=
  -1/b*Subst[Int[ReplaceAll[u,x->-a/b+Cos[x]/b]*f^(c*x^n)*Sin[x],x],x,ArcCos[a+b*x]] /;
FreeQ[{a,b,c,f},x] && IGtQ[n,0]


Int[ArcSin[a_.*x_^2+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
  x*ArcSin[a*x^2+b*Sqrt[c+d*x^2]] - 
  x*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]/Sqrt[(-x^2)*(b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2])]*
    Int[x*(b*d+2*a*Sqrt[c+d*x^2])/(Sqrt[c+d*x^2]*Sqrt[b^2*d +a^2*x^2+2*a*b*Sqrt[c+d*x^2]]),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2*c,1]


Int[ArcCos[a_.*x_^2+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
  x*ArcCos[a*x^2+b*Sqrt[c+d*x^2]] + 
  x*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]/Sqrt[(-x^2)*(b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2])]*
    Int[x*(b*d+2*a*Sqrt[c+d*x^2])/(Sqrt[c+d*x^2]*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2*c,1]


Int[ArcSin[u_],x_Symbol] :=
  x*ArcSin[u] -
  Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1-u^2],x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCos[u_],x_Symbol] :=
  x*ArcCos[u] +
  Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1-u^2],x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSin[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcSin[u])/(d*(m+1)) -
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCos[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCos[u])/(d*(m+1)) +
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSin[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcSin[u]),w,x] -
  b*Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCos[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCos[u]),w,x] +
  b*Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]





(* ::Subsection::Closed:: *)
(*5.2.1 u (a+b arctan(c x^n))^p*)


Int[(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^p - 
  b*c*p*Int[x*(a+b*ArcTan[c*x])^(p-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  x*(a+b*ArcCot[c*x])^p + 
  b*c*p*Int[x*(a+b*ArcCot[c*x])^(p-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcTan[c_.*x_])/x_,x_Symbol] :=
  a*Log[x] + I*b/2*Int[Log[1-I*c*x]/x,x] - I*b/2*Int[Log[1+I*c*x]/x,x] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcCot[c_.*x_])/x_,x_Symbol] :=
  a*Log[x] + I*b/2*Int[Log[1-I/(c*x)]/x,x] - I*b/2*Int[Log[1+I/(c*x)]/x,x] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_/x_,x_Symbol] :=
  2*(a+b*ArcTan[c*x])^p*ArcTanh[1-2/(1+I*c*x)] - 
  2*b*c*p*Int[(a+b*ArcTan[c*x])^(p-1)*ArcTanh[1-2/(1+I*c*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IGtQ[p,1]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_/x_,x_Symbol] :=
  2*(a+b*ArcCot[c*x])^p*ArcCoth[1-2/(1+I*c*x)] + 
  2*b*c*p*Int[(a+b*ArcCot[c*x])^(p-1)*ArcCoth[1-2/(1+I*c*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IGtQ[p,1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcTan[c*x])^p/(d*(m+1)) - 
  b*c*p/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcTan[c*x])^(p-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[p,0] && (EqQ[p,1] || IntegerQ[m]) && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCot[c*x])^p/(d*(m+1)) + 
  b*c*p/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcCot[c*x])^(p-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[p,0] && (EqQ[p,1] || IntegerQ[m]) && NeQ[m,-1]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTan[c*x])^p*Log[2/(1+e*x/d)]/e + 
  b*c*p/e*Int[(a+b*ArcTan[c*x])^(p-1)*Log[2/(1+e*x/d)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCot[c*x])^p*Log[2/(1+e*x/d)]/e - 
  b*c*p/e*Int[(a+b*ArcCot[c*x])^(p-1)*Log[2/(1+e*x/d)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0]


Int[(a_.+b_.*ArcTan[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTan[c*x])*Log[2/(1-I*c*x)]/e + 
  b*c/e*Int[Log[2/(1-I*c*x)]/(1+c^2*x^2),x] + 
  (a+b*ArcTan[c*x])*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e - 
  b*c/e*Int[Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCot[c*x])*Log[2/(1-I*c*x)]/e - 
  b*c/e*Int[Log[2/(1-I*c*x)]/(1+c^2*x^2),x] + 
  (a+b*ArcCot[c*x])*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e + 
  b*c/e*Int[Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^2/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTan[c*x])^2*Log[2/(1-I*c*x)]/e + 
  I*b*(a+b*ArcTan[c*x])*PolyLog[2,1-2/(1-I*c*x)]/e - 
  b^2*PolyLog[3,1-2/(1-I*c*x)]/(2*e) + 
  (a+b*ArcTan[c*x])^2*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e - 
  I*b*(a+b*ArcTan[c*x])*PolyLog[2,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e + 
  b^2*PolyLog[3,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^2/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCot[c*x])^2*Log[2/(1-I*c*x)]/e - 
  I*b*(a+b*ArcCot[c*x])*PolyLog[2,1-2/(1-I*c*x)]/e - 
  b^2*PolyLog[3,1-2/(1-I*c*x)]/(2*e) + 
  (a+b*ArcCot[c*x])^2*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e + 
  I*b*(a+b*ArcCot[c*x])*PolyLog[2,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e + 
  b^2*PolyLog[3,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^3/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTan[c*x])^3*Log[2/(1-I*c*x)]/e + 
  3*I*b*(a+b*ArcTan[c*x])^2*PolyLog[2,1-2/(1-I*c*x)]/(2*e) - 
  3*b^2*(a+b*ArcTan[c*x])*PolyLog[3,1-2/(1-I*c*x)]/(2*e) - 
  3*I*b^3*PolyLog[4,1-2/(1-I*c*x)]/(4*e) + 
  (a+b*ArcTan[c*x])^3*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e - 
  3*I*b*(a+b*ArcTan[c*x])^2*PolyLog[2,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) + 
  3*b^2*(a+b*ArcTan[c*x])*PolyLog[3,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) + 
  3*I*b^3*PolyLog[4,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(4*e) /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^3/(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCot[c*x])^3*Log[2/(1-I*c*x)]/e - 
  3*I*b*(a+b*ArcCot[c*x])^2*PolyLog[2,1-2/(1-I*c*x)]/(2*e) - 
  3*b^2*(a+b*ArcCot[c*x])*PolyLog[3,1-2/(1-I*c*x)]/(2*e) + 
  3*I*b^3*PolyLog[4,1-2/(1-I*c*x)]/(4*e) + 
  (a+b*ArcCot[c*x])^3*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e + 
  3*I*b*(a+b*ArcCot[c*x])^2*PolyLog[2,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) + 
  3*b^2*(a+b*ArcCot[c*x])*PolyLog[3,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) - 
  3*I*b^3*PolyLog[4,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(4*e) /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcTan[c*x])/(e*(q+1)) - 
  b*c/(e*(q+1))*Int[(d+e*x)^(q+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcCot[c*x])/(e*(q+1)) + 
  b*c/(e*(q+1))*Int[(d+e*x)^(q+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_,x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcTan[c*x])^p/(e*(q+1)) - 
  b*c*p/(e*(q+1))*Int[ExpandIntegrand[(a+b*ArcTan[c*x])^(p-1),(d+e*x)^(q+1)/(1+c^2*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,1] && IntegerQ[q] && NeQ[q,-1]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_,x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*ArcCot[c*x])^p/(e*(q+1)) + 
  b*c*p/(e*(q+1))*Int[ExpandIntegrand[(a+b*ArcCot[c*x])^(p-1),(d+e*x)^(q+1)/(1+c^2*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,1] && IntegerQ[q] && NeQ[q,-1]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  f/e*Int[(f*x)^(m-1)*(a+b*ArcTan[c*x])^p,x] - 
  d*f/e*Int[(f*x)^(m-1)*(a+b*ArcTan[c*x])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0] && GtQ[m,0]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  f/e*Int[(f*x)^(m-1)*(a+b*ArcCot[c*x])^p,x] - 
  d*f/e*Int[(f*x)^(m-1)*(a+b*ArcCot[c*x])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0] && GtQ[m,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcTan[c*x])^p*Log[2-2/(1+e*x/d)]/d - 
  b*c*p/d*Int[(a+b*ArcTan[c*x])^(p-1)*Log[2-2/(1+e*x/d)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcCot[c*x])^p*Log[2-2/(1+e*x/d)]/d + 
  b*c*p/d*Int[(a+b*ArcCot[c*x])^(p-1)*Log[2-2/(1+e*x/d)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[(f*x)^m*(a+b*ArcTan[c*x])^p,x] - 
  e/(d*f)*Int[(f*x)^(m+1)*(a+b*ArcTan[c*x])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[(f*x)^m*(a+b*ArcCot[c*x])^p,x] - 
  e/(d*f)*Int[(f*x)^(m+1)*(a+b*ArcCot[c*x])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0] && LtQ[m,-1]


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcTan[c*x]),u] - b*c*Int[SimplifyIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,q},x] && NeQ[q,-1] && IntegerQ[2*m] && (IGtQ[m,0] && IGtQ[q,0] || ILtQ[m+q+1,0] && LtQ[m*q,0])


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcCot[c*x]),u] + b*c*Int[SimplifyIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,q},x] && NeQ[q,-1] && IntegerQ[2*m] && (IGtQ[m,0] && IGtQ[q,0] || ILtQ[m+q+1,0] && LtQ[m*q,0])


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_,x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcTan[c*x])^p,u] - b*c*p*Int[ExpandIntegrand[(a+b*ArcTan[c*x])^(p-1),u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,q},x] && IGtQ[p,1] && EqQ[c^2*d^2+e^2,0] && IntegersQ[m,q] && NeQ[m,-1] && NeQ[q,-1] && ILtQ[m+q+1,0] && LtQ[m*q,0]


Int[(f_.*x_)^m_.*(d_.+e_.*x_)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_,x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x)^q,x]},
  Dist[(a+b*ArcCot[c*x])^p,u] + b*c*p*Int[ExpandIntegrand[(a+b*ArcCot[c*x])^(p-1),u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,q},x] && IGtQ[p,1] && EqQ[c^2*d^2+e^2,0] && IntegersQ[m,q] && NeQ[m,-1] && NeQ[q,-1] && ILtQ[m+q+1,0] && LtQ[m*q,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTan[c*x])^p,(f*x)^m*(d+e*x)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0] && IntegerQ[q] && (GtQ[q,0] || NeQ[a,0] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCot[c*x])^p,(f*x)^m*(d+e*x)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0] && IntegerQ[q] && (GtQ[q,0] || NeQ[a,0] || IntegerQ[m])


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^q/(2*c*q*(2*q+1)) + 
  x*(d+e*x^2)^q*(a+b*ArcTan[c*x])/(2*q+1) + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[q,0]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^q/(2*c*q*(2*q+1)) + 
  x*(d+e*x^2)^q*(a+b*ArcCot[c*x])/(2*q+1) + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[q,0]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_,x_Symbol] :=
  -b*p*(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p-1)/(2*c*q*(2*q+1)) + 
  x*(d+e*x^2)^q*(a+b*ArcTan[c*x])^p/(2*q+1) + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*ArcTan[c*x])^p,x] + 
  b^2*d*p*(p-1)/(2*q*(2*q+1))*Int[(d+e*x^2)^(q-1)*(a+b*ArcTan[c*x])^(p-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[q,0] && GtQ[p,1]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_,x_Symbol] :=
  b*p*(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p-1)/(2*c*q*(2*q+1)) + 
  x*(d+e*x^2)^q*(a+b*ArcCot[c*x])^p/(2*q+1) + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*ArcCot[c*x])^p,x] + 
  b^2*d*p*(p-1)/(2*q*(2*q+1))*Int[(d+e*x^2)^(q-1)*(a+b*ArcCot[c*x])^(p-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[q,0] && GtQ[p,1]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcTan[c_.*x_])),x_Symbol] :=
  Log[RemoveContent[a+b*ArcTan[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCot[c_.*x_])),x_Symbol] :=
  -Log[RemoveContent[a+b*ArcCot[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTan[c*x])^(p+1)/(b*c*d*(p+1)) /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && NeQ[p,-1]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCot[c*x])^(p+1)/(b*c*d*(p+1)) /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && NeQ[p,-1]


Int[(a_.+b_.*ArcTan[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*I*(a+b*ArcTan[c*x])*ArcTan[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,-I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[d,0]


Int[(a_.+b_.*ArcCot[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*I*(a+b*ArcCot[c*x])*ArcTan[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,-I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[d,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c*Sqrt[d])*Subst[Int[(a+b*x)^p*Sec[x],x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && GtQ[d,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -x*Sqrt[1+1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^p*Csc[x],x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && GtQ[d,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTan[c*x])^p/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCot[c*x])^p/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^p/(2*d*(d+e*x^2)) + 
  (a+b*ArcTan[c*x])^(p+1)/(2*b*c*d^2*(p+1)) - 
  b*c*p/2*Int[x*(a+b*ArcTan[c*x])^(p-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcCot[c*x])^p/(2*d*(d+e*x^2)) - 
  (a+b*ArcCot[c*x])^(p+1)/(2*b*c*d^2*(p+1)) + 
  b*c*p/2*Int[x*(a+b*ArcCot[c*x])^(p-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,0]


Int[(a_.+b_.*ArcTan[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTan[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d]


Int[(a_.+b_.*ArcCot[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCot[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^(q+1)/(4*c*d*(q+1)^2) -
  x*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])/(2*d*(q+1)) +
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[q,-1] && NeQ[q,-3/2]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(q+1)/(4*c*d*(q+1)^2) -
  x*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])/(2*d*(q+1)) +
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[q,-1] && NeQ[q,-3/2]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  b*p*(a+b*ArcTan[c*x])^(p-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTan[c*x])^p/(d*Sqrt[d+e*x^2]) -
  b^2*p*(p-1)*Int[(a+b*ArcTan[c*x])^(p-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,1]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b*p*(a+b*ArcCot[c*x])^(p-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCot[c*x])^p/(d*Sqrt[d+e*x^2]) -
  b^2*p*(p-1)*Int[(a+b*ArcCot[c*x])^(p-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,1]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_,x_Symbol] :=
  b*p*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^(p-1)/(4*c*d*(q+1)^2) -
  x*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^p/(2*d*(q+1)) +
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^p,x] -
  b^2*p*(p-1)/(4*(q+1)^2)*Int[(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[q,-1] && GtQ[p,1] && NeQ[q,-3/2]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_,x_Symbol] :=
  -b*p*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^(p-1)/(4*c*d*(q+1)^2) -
  x*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^p/(2*d*(q+1)) +
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^p,x] -
  b^2*p*(p-1)/(4*(q+1)^2)*Int[(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[q,-1] && GtQ[p,1] && NeQ[q,-3/2]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_,x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^(p+1)/(b*c*d*(p+1)) - 
  2*c*(q+1)/(b*(p+1))*Int[x*(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[q,-1] && LtQ[p,-1]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_,x_Symbol] :=
  -(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^(p+1)/(b*c*d*(p+1)) + 
  2*c*(q+1)/(b*(p+1))*Int[x*(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[q,-1] && LtQ[p,-1]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  d^q/c*Subst[Int[(a+b*x)^p/Cos[x]^(2*(q+1)),x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && ILtQ[2*(q+1),0] && (IntegerQ[q] || GtQ[d,0])


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  d^(q+1/2)*Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(1+c^2*x^2)^q*(a+b*ArcTan[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && ILtQ[2*(q+1),0] && Not[IntegerQ[q] || GtQ[d,0]]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  -d^q/c*Subst[Int[(a+b*x)^p/Sin[x]^(2*(q+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && ILtQ[2*(q+1),0] && IntegerQ[q]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  -d^(q+1/2)*x*Sqrt[(1+c^2*x^2)/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^p/Sin[x]^(2*(q+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && ILtQ[2*(q+1),0] && Not[IntegerQ[q]]


Int[ArcTan[c_.*x_]/(d_.+e_.*x_^2),x_Symbol] :=
  I/2*Int[Log[1-I*c*x]/(d+e*x^2),x] - I/2*Int[Log[1+I*c*x]/(d+e*x^2),x] /;
FreeQ[{c,d,e},x]


Int[ArcCot[c_.*x_]/(d_.+e_.*x_^2),x_Symbol] :=
  I/2*Int[Log[1-I/(c*x)]/(d+e*x^2),x] - I/2*Int[Log[1+I/(c*x)]/(d+e*x^2),x] /;
FreeQ[{c,d,e},x]


Int[(a_+b_.*ArcTan[c_.*x_])/(d_.+e_.*x_^2),x_Symbol] :=
  a*Int[1/(d+e*x^2),x] + b*Int[ArcTan[c*x]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(a_+b_.*ArcCot[c_.*x_])/(d_.+e_.*x_^2),x_Symbol] :=
  a*Int[1/(d+e*x^2),x] + b*Int[ArcCot[c*x]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^q,x]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[u/(1+c^2*x^2),x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[q] || ILtQ[q+1/2,0])


Int[(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^q,x]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[u/(1+c^2*x^2),x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[q] || ILtQ[q+1/2,0])


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTan[c*x])^p,(d+e*x^2)^q,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[q] && IGtQ[p,0]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCot[c*x])^p,(d+e*x^2)^q,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[q] && IGtQ[p,0]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  f^2/e*Int[(f*x)^(m-2)*(a+b*ArcTan[c*x])^p,x] -
  d*f^2/e*Int[(f*x)^(m-2)*(a+b*ArcTan[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,0] && GtQ[m,1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  f^2/e*Int[(f*x)^(m-2)*(a+b*ArcCot[c*x])^p,x] -
  d*f^2/e*Int[(f*x)^(m-2)*(a+b*ArcCot[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,0] && GtQ[m,1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[(f*x)^m*(a+b*ArcTan[c*x])^p,x] -
  e/(d*f^2)*Int[(f*x)^(m+2)*(a+b*ArcTan[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,0] && LtQ[m,-1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[(f*x)^m*(a+b*ArcCot[c*x])^p,x] -
  e/(d*f^2)*Int[(f*x)^(m+2)*(a+b*ArcCot[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,0] && LtQ[m,-1]


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^(p+1)/(b*e*(p+1)) - 
  1/(c*d)*Int[(a+b*ArcTan[c*x])^p/(I-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^(p+1)/(b*e*(p+1)) - 
  1/(c*d)*Int[(a+b*ArcCot[c*x])^p/(I-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0]


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^p_/(d_+e_.*x_^2),x_Symbol] :=
  x*(a+b*ArcTan[c*x])^(p+1)/(b*c*d*(p+1)) - 
  1/(b*c*d*(p+1))*Int[(a+b*ArcTan[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && Not[IGtQ[p,0]] && NeQ[p,-1]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^p_/(d_+e_.*x_^2),x_Symbol] :=
  -x*(a+b*ArcCot[c*x])^(p+1)/(b*c*d*(p+1)) + 
  1/(b*c*d*(p+1))*Int[(a+b*ArcCot[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && Not[IGtQ[p,0]] && NeQ[p,-1]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^(p+1)/(b*d*(p+1)) +
  I/d*Int[(a+b*ArcTan[c*x])^p/(x*(I+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^(p+1)/(b*d*(p+1)) +
  I/d*Int[(a+b*ArcCot[c*x])^p/(x*(I+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,0]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTan[c_.*x_])^p_/(d_+e_.*x_^2),x_Symbol] :=
  (f*x)^m*(a+b*ArcTan[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*d*(p+1))*Int[(f*x)^(m-1)*(a+b*ArcTan[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && LtQ[p,-1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCot[c_.*x_])^p_/(d_+e_.*x_^2),x_Symbol] :=
  -(f*x)^m*(a+b*ArcCot[c*x])^(p+1)/(b*c*d*(p+1)) + 
  f*m/(b*c*d*(p+1))*Int[(f*x)^(m-1)*(a+b*ArcCot[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && LtQ[p,-1]


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTan[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[EqQ[m,1] && NeQ[a,0]]


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCot[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[EqQ[m,1] && NeQ[a,0]]


Int[x_*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^p/(2*e*(q+1)) - 
  b*p/(2*c*(q+1))*Int[(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,q},x] && EqQ[e,c^2*d] && GtQ[p,0] && NeQ[q,-1]


Int[x_*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^p/(2*e*(q+1)) +
  b*p/(2*c*(q+1))*Int[(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,q},x] && EqQ[e,c^2*d] && GtQ[p,0] && NeQ[q,-1]


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^p_/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^(p+1)/(b*c*d*(p+1)*(d+e*x^2)) -
  (1-c^2*x^2)*(a+b*ArcTan[c*x])^(p+2)/(b^2*e*(p+1)*(p+2)*(d+e*x^2)) -
  4/(b^2*(p+1)*(p+2))*Int[x*(a+b*ArcTan[c*x])^(p+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[p,-1] && NeQ[p,-2]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^p_/(d_+e_.*x_^2)^2,x_Symbol] :=
  -x*(a+b*ArcCot[c*x])^(p+1)/(b*c*d*(p+1)*(d+e*x^2)) -
  (1-c^2*x^2)*(a+b*ArcCot[c*x])^(p+2)/(b^2*e*(p+1)*(p+2)*(d+e*x^2)) -
  4/(b^2*(p+1)*(p+2))*Int[x*(a+b*ArcCot[c*x])^(p+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[p,-1] && NeQ[p,-2]


Int[x_^2*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(q+1)/(4*c^3*d*(q+1)^2) + 
  x*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])/(2*c^2*d*(q+1)) - 
  1/(2*c^2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[q,-1] && NeQ[q,-5/2]


Int[x_^2*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^(q+1)/(4*c^3*d*(q+1)^2) + 
  x*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])/(2*c^2*d*(q+1)) - 
  1/(2*c^2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && LtQ[q,-1] && NeQ[q,-5/2]


Int[x_^2*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  (a+b*ArcTan[c*x])^(p+1)/(2*b*c^3*d^2*(p+1)) - 
  x*(a+b*ArcTan[c*x])^p/(2*c^2*d*(d+e*x^2)) + 
  b*p/(2*c)*Int[x*(a+b*ArcTan[c*x])^(p-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,0]


Int[x_^2*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  -(a+b*ArcCot[c*x])^(p+1)/(2*b*c^3*d^2*(p+1)) - 
  x*(a+b*ArcCot[c*x])^p/(2*c^2*d*(d+e*x^2)) - 
  b*p/(2*c)*Int[x*(a+b*ArcCot[c*x])^(p-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  b*(f*x)^m*(d+e*x^2)^(q+1)/(c*d*m^2) - 
  f*(f*x)^(m-1)*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])/(c^2*d*m) + 
  f^2*(m-1)/(c^2*d*m)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && EqQ[m+2*q+2,0] && LtQ[q,-1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  -b*(f*x)^m*(d+e*x^2)^(q+1)/(c*d*m^2) - 
  f*(f*x)^(m-1)*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])/(c^2*d*m) + 
  f^2*(m-1)/(c^2*d*m)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && EqQ[m+2*q+2,0] && LtQ[q,-1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_,x_Symbol] :=
  b*p*(f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^(p-1)/(c*d*m^2) - 
  f*(f*x)^(m-1)*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^p/(c^2*d*m) - 
  b^2*p*(p-1)/m^2*Int[(f*x)^m*(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p-2),x] + 
  f^2*(m-1)/(c^2*d*m)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && EqQ[m+2*q+2,0] && LtQ[q,-1] && GtQ[p,1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_,x_Symbol] :=
  -b*p*(f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^(p-1)/(c*d*m^2) - 
  f*(f*x)^(m-1)*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^p/(c^2*d*m) - 
  b^2*p*(p-1)/m^2*Int[(f*x)^m*(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p-2),x] + 
  f^2*(m-1)/(c^2*d*m)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && EqQ[m+2*q+2,0] && LtQ[q,-1] && GtQ[p,1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_,x_Symbol] :=
  (f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*(p+1))*Int[(f*x)^(m-1)*(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[e,c^2*d] && EqQ[m+2*q+2,0] && LtQ[p,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_,x_Symbol] :=
  -(f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^(p+1)/(b*c*d*(p+1)) + 
  f*m/(b*c*(p+1))*Int[(f*x)^(m-1)*(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[e,c^2*d] && EqQ[m+2*q+2,0] && LtQ[p,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^p/(d*f*(m+1)) - 
  b*c*p/(f*(m+1))*Int[(f*x)^(m+1)*(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[e,c^2*d] && EqQ[m+2*q+3,0] && GtQ[p,0] && NeQ[m,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^p/(d*f*(m+1)) + 
  b*c*p/(f*(m+1))*Int[(f*x)^(m+1)*(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[e,c^2*d] && EqQ[m+2*q+3,0] && GtQ[p,0] && NeQ[m,-1]


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])/(f*(m+2)) - 
  b*c*d/(f*(m+2))*Int[(f*x)^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[(f*x)^m*(a+b*ArcTan[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && NeQ[m,-2]


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])/(f*(m+2)) + 
  b*c*d/(f*(m+2))*Int[(f*x)^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[(f*x)^m*(a+b*ArcCot[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && NeQ[m,-2]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q*(a+b*ArcTan[c*x])^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && IGtQ[p,0] && IGtQ[q,1] && (EqQ[p,1] || IntegerQ[m])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q*(a+b*ArcCot[c*x])^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && IGtQ[p,0] && IGtQ[q,1] && (EqQ[p,1] || IntegerQ[m])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  d*Int[(f*x)^m*(d+e*x^2)^(q-1)*(a+b*ArcTan[c*x])^p,x] + 
  c^2*d/f^2*Int[(f*x)^(m+2)*(d+e*x^2)^(q-1)*(a+b*ArcTan[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[q,0] && IGtQ[p,0] && (RationalQ[m] || EqQ[p,1] && IntegerQ[q])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  d*Int[(f*x)^m*(d+e*x^2)^(q-1)*(a+b*ArcCot[c*x])^p,x] + 
  c^2*d/f^2*Int[(f*x)^(m+2)*(d+e*x^2)^(q-1)*(a+b*ArcCot[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[q,0] && IGtQ[p,0] && (RationalQ[m] || EqQ[p,1] && IntegerQ[q])


Int[(f_.*x_)^m_*(a_.+b_.*ArcTan[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^p/(c^2*d*m) - 
  b*f*p/(c*m)*Int[(f*x)^(m-1)*(a+b*ArcTan[c*x])^(p-1)/Sqrt[d+e*x^2],x] - 
  f^2*(m-1)/(c^2*m)*Int[(f*x)^(m-2)*(a+b*ArcTan[c*x])^p/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[p,0] && GtQ[m,1]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCot[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^p/(c^2*d*m) + 
  b*f*p/(c*m)*Int[(f*x)^(m-1)*(a+b*ArcCot[c*x])^(p-1)/Sqrt[d+e*x^2],x] - 
  f^2*(m-1)/(c^2*m)*Int[(f*x)^(m-2)*(a+b*ArcCot[c*x])^p/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[p,0] && GtQ[m,1]


Int[(a_.+b_.*ArcTan[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcTan[c*x])*ArcTanh[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] + 
  I*b/Sqrt[d]*PolyLog[2,-Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] - 
  I*b/Sqrt[d]*PolyLog[2,Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[d,0]


Int[(a_.+b_.*ArcCot[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcCot[c*x])*ArcTanh[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] - 
  I*b/Sqrt[d]*PolyLog[2,-Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] + 
  I*b/Sqrt[d]*PolyLog[2,Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[d,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  1/Sqrt[d]*Subst[Int[(a+b*x)^p*Csc[x],x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && GtQ[d,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -c*x*Sqrt[1+1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^p*Sec[x],x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && GtQ[d,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTan[c*x])^p/(x*Sqrt[1+c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCot[c*x])^p/(x*Sqrt[1+c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && Not[GtQ[d,0]]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^p/(d*x) + 
  b*c*p*Int[(a+b*ArcTan[c*x])^(p-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^p/(d*x) - 
  b*c*p*Int[(a+b*ArcCot[c*x])^(p-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[p,0]


Int[(f_.*x_)^m_*(a_.+b_.*ArcTan[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^p/(d*f*(m+1)) - 
  b*c*p/(f*(m+1))*Int[(f*x)^(m+1)*(a+b*ArcTan[c*x])^(p-1)/Sqrt[d+e*x^2],x] - 
  c^2*(m+2)/(f^2*(m+1))*Int[(f*x)^(m+2)*(a+b*ArcTan[c*x])^p/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[p,0] && LtQ[m,-1] && NeQ[m,-2]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCot[c_.*x_])^p_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^p/(d*f*(m+1)) + 
  b*c*p/(f*(m+1))*Int[(f*x)^(m+1)*(a+b*ArcCot[c*x])^(p-1)/Sqrt[d+e*x^2],x] - 
  c^2*(m+2)/(f^2*(m+1))*Int[(f*x)^(m+2)*(a+b*ArcCot[c*x])^p/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[p,0] && LtQ[m,-1] && NeQ[m,-2]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^p,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^q*(a+b*ArcTan[c*x])^p,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IntegersQ[p,2*q] && LtQ[q,-1] && IGtQ[m,1] && NeQ[p,-1]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^p,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^q*(a+b*ArcCot[c*x])^p,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IntegersQ[p,2*q] && LtQ[q,-1] && IGtQ[m,1] && NeQ[p,-1]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^p,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^q*(a+b*ArcTan[c*x])^p,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IntegersQ[p,2*q] && LtQ[q,-1] && ILtQ[m,0] && NeQ[p,-1]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^p,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^q*(a+b*ArcCot[c*x])^p,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IntegersQ[p,2*q] && LtQ[q,-1] && ILtQ[m,0] && NeQ[p,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  (f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])^(p+1)/(b*c*d*(p+1)) - 
  f*m/(b*c*(p+1))*Int[(f*x)^(m-1)*(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p+1),x] - 
  c*f*(m+2*q+2)/(b*(p+1))*Int[(f*x)^(m+1)*(d+e*x^2)^q*(a+b*ArcTan[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && RationalQ[m] && LtQ[q,-1] && LtQ[p,-1] && NeQ[m+2*q+2,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  -(f*x)^m*(d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])^(p+1)/(b*c*d*(p+1)) + 
  f*m/(b*c*(p+1))*Int[(f*x)^(m-1)*(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p+1),x] + 
  c*f*(m+2*q+2)/(b*(p+1))*Int[(f*x)^(m+1)*(d+e*x^2)^q*(a+b*ArcCot[c*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && RationalQ[m] && LtQ[q,-1] && LtQ[p,-1] && NeQ[m+2*q+2,0]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  d^q/c^(m+1)*Subst[Int[(a+b*x)^p*Sin[x]^m/Cos[x]^(m+2*(q+1)),x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && IGtQ[m,0] && ILtQ[m+2*q+1,0] && (IntegerQ[q] || GtQ[d,0])


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  d^(q+1/2)*Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[x^m*(1+c^2*x^2)^q*(a+b*ArcTan[c*x])^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && IGtQ[m,0] && ILtQ[m+2*q+1,0] && Not[IntegerQ[q] || GtQ[d,0]]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  -d^q/c^(m+1)*Subst[Int[(a+b*x)^p*Cos[x]^m/Sin[x]^(m+2*(q+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && IGtQ[m,0] && ILtQ[m+2*q+1,0] && IntegerQ[q]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  -d^(q+1/2)*x*Sqrt[(1+c^2*x^2)/(c^2*x^2)]/(c^m*Sqrt[d+e*x^2])*Subst[Int[(a+b*x)^p*Cos[x]^m/Sin[x]^(m+2*(q+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && IGtQ[m,0] && ILtQ[m+2*q+1,0] && Not[IntegerQ[q]]


Int[x_*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcTan[c*x])/(2*e*(q+1)) - 
  b*c/(2*e*(q+1))*Int[(d+e*x^2)^(q+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]


Int[x_*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(q+1)*(a+b*ArcCot[c*x])/(2*e*(q+1)) + 
  b*c/(2*e*(q+1))*Int[(d+e*x^2)^(q+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^q,x]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && (
  IGtQ[q,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*q+3,0]] || 
  IGtQ[(m+1)/2,0] && Not[ILtQ[q,0] && GtQ[m+2*q+3,0]] || 
  ILtQ[(m+2*q+1)/2,0] && Not[ILtQ[(m-1)/2,0]] )


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^q,x]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && (
  IGtQ[q,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*q+3,0]] || 
  IGtQ[(m+1)/2,0] && Not[ILtQ[q,0] && GtQ[m+2*q+3,0]] || 
  ILtQ[(m+2*q+1)/2,0] && Not[ILtQ[(m-1)/2,0]] )


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  1/(4*d^2*Rt[-e/d,2])*Int[(a+b*ArcTan[c*x])^p/(1-Rt[-e/d,2]*x)^2,x] - 
  1/(4*d^2*Rt[-e/d,2])*Int[(a+b*ArcTan[c*x])^p/(1+Rt[-e/d,2]*x)^2,x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2)^2,x_Symbol] :=
  1/(4*d^2*Rt[-e/d,2])*Int[(a+b*ArcCot[c*x])^p/(1-Rt[-e/d,2]*x)^2,x] - 
  1/(4*d^2*Rt[-e/d,2])*Int[(a+b*ArcCot[c*x])^p/(1+Rt[-e/d,2]*x)^2,x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*ArcTan[c*x])^p,(f*x)^m*(d+e*x^2)^q,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[q] && IGtQ[p,0] && (EqQ[p,1] && GtQ[q,0] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*ArcCot[c*x])^p,(f*x)^m*(d+e*x^2)^q,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[q] && IGtQ[p,0] && (EqQ[p,1] && GtQ[q,0] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  a*Int[(f*x)^m*(d+e*x^2)^q,x] + b*Int[(f*x)^m*(d+e*x^2)^q*ArcTan[c*x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  a*Int[(f*x)^m*(d+e*x^2)^q,x] + b*Int[(f*x)^m*(d+e*x^2)^q*ArcCot[c*x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTan[c*x])^p/(d+e*x^2),(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && EqQ[e,c^2*d] && IGtQ[m,0]


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCot[c*x])^p/(d+e*x^2),(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && EqQ[e,c^2*d] && IGtQ[m,0]


Int[ArcTanh[u_]*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTan[c*x])^p/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTan[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[u^2-(1-2*I/(I+c*x))^2,0]


Int[ArcCoth[u_]*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCot[c*x])^p/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCot[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[u^2-(1-2*I/(I+c*x))^2,0]


Int[ArcTanh[u_]*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTan[c*x])^p/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTan[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[u^2-(1-2*I/(I-c*x))^2,0]


Int[ArcCoth[u_]*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCot[c*x])^p/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCot[c*x])^p/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[u^2-(1-2*I/(I-c*x))^2,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_.*Log[f_+g_.*x_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTan[c*x])^(p+1)*Log[f+g*x]/(b*c*d*(p+1)) - 
  g/(b*c*d*(p+1))*Int[(a+b*ArcTan[c*x])^(p+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[c^2*f^2+g^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_.*Log[f_+g_.*x_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCot[c*x])^(p+1)*Log[f+g*x]/(b*c*d*(p+1)) - 
  g/(b*c*d*(p+1))*Int[(a+b*ArcCot[c*x])^(p+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[c^2*f^2+g^2,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcTan[c*x])^p*PolyLog[2,1-u]/(2*c*d) -
  b*p*I/2*Int[(a+b*ArcTan[c*x])^(p-1)*PolyLog[2,1-u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[(1-u)^2-(1-2*I/(I+c*x))^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^p*PolyLog[2,1-u]/(2*c*d) +
  b*p*I/2*Int[(a+b*ArcCot[c*x])^(p-1)*PolyLog[2,1-u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[(1-u)^2-(1-2*I/(I+c*x))^2,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^p*PolyLog[2,1-u]/(2*c*d) +
  b*p*I/2*Int[(a+b*ArcTan[c*x])^(p-1)*PolyLog[2,1-u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[(1-u)^2-(1-2*I/(I-c*x))^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcCot[c*x])^p*PolyLog[2,1-u]/(2*c*d) -
  b*p*I/2*Int[(a+b*ArcCot[c*x])^(p-1)*PolyLog[2,1-u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[(1-u)^2-(1-2*I/(I-c*x))^2,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_.*PolyLog[k_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^p*PolyLog[k+1,u]/(2*c*d) +
  b*p*I/2*Int[(a+b*ArcTan[c*x])^(p-1)*PolyLog[k+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,k},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[u^2-(1-2*I/(I+c*x))^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_.*PolyLog[k_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcCot[c*x])^p*PolyLog[k+1,u]/(2*c*d) -
  b*p*I/2*Int[(a+b*ArcCot[c*x])^(p-1)*PolyLog[k+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,k},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[u^2-(1-2*I/(I+c*x))^2,0]


Int[(a_.+b_.*ArcTan[c_.*x_])^p_.*PolyLog[k_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcTan[c*x])^p*PolyLog[k+1,u]/(2*c*d) -
  b*p*I/2*Int[(a+b*ArcTan[c*x])^(p-1)*PolyLog[k+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,k},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[u^2-(1-2*I/(I-c*x))^2,0]


Int[(a_.+b_.*ArcCot[c_.*x_])^p_.*PolyLog[k_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^p*PolyLog[k+1,u]/(2*c*d) +
  b*p*I/2*Int[(a+b*ArcCot[c*x])^(p-1)*PolyLog[k+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,k},x] && IGtQ[p,0] && EqQ[e,c^2*d] && EqQ[u^2-(1-2*I/(I-c*x))^2,0]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCot[c_.*x_])*(a_.+b_.*ArcTan[c_.*x_])),x_Symbol] :=
  (-Log[a+b*ArcCot[c*x]]+Log[a+b*ArcTan[c*x]])/(b*c*d*(2*a+b*ArcCot[c*x]+b*ArcTan[c*x])) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d]


Int[(a_.+b_.*ArcCot[c_.*x_])^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCot[c*x])^(q+1)*(a+b*ArcTan[c*x])^p/(b*c*d*(q+1)) +
  p/(q+1)*Int[(a+b*ArcCot[c*x])^(q+1)*(a+b*ArcTan[c*x])^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && IGeQ[q,p]


Int[(a_.+b_.*ArcTan[c_.*x_])^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTan[c*x])^(q+1)*(a+b*ArcCot[c*x])^p/(b*c*d*(q+1)) +
  p/(q+1)*Int[(a+b*ArcTan[c*x])^(q+1)*(a+b*ArcCot[c*x])^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0] && IGeQ[q,p]


Int[ArcTan[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I*a*x]/(c+d*x^n),x] -
  I/2*Int[Log[1+I*a*x]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[EqQ[n,2] && EqQ[d,a^2*c]]


Int[ArcCot[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I/(a*x)]/(c+d*x^n),x] -
  I/2*Int[Log[1+I/(a*x)]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[EqQ[n,2] && EqQ[d,a^2*c]]


Int[Log[d_.*x_^m_.]*ArcTan[c_.*x_^n_.]/x_,x_Symbol] :=
  I/2*Int[Log[d*x^m]*Log[1-I*c*x^n]/x,x] - I/2*Int[Log[d*x^m]*Log[1+I*c*x^n]/x,x] /;
FreeQ[{c,d,m,n},x]


Int[Log[d_.*x_^m_.]*ArcCot[c_.*x_^n_.]/x_,x_Symbol] :=
  I/2*Int[Log[d*x^m]*Log[1-I/(c*x^n)]/x,x] - I/2*Int[Log[d*x^m]*Log[1+I/(c*x^n)]/x,x] /;
FreeQ[{c,d,m,n},x]


Int[Log[d_.*x_^m_.]*(a_+b_.*ArcTan[c_.*x_^n_.])/x_,x_Symbol] :=
  a*Int[Log[d*x^m]/x,x] + b*Int[(Log[d*x^m]*ArcTan[c*x^n])/x,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[Log[d_.*x_^m_.]*(a_+b_.*ArcCot[c_.*x_^n_.])/x_,x_Symbol] :=
  a*Int[Log[d*x^m]/x,x] + b*Int[(Log[d*x^m]*ArcCot[c*x^n])/x,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  x*(d+e*Log[f+g*x^2])*(a+b*ArcTan[c*x]) - 
  2*e*g*Int[x^2*(a+b*ArcTan[c*x])/(f+g*x^2),x] - 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  x*(d+e*Log[f+g*x^2])*(a+b*ArcCot[c*x]) - 
  2*e*g*Int[x^2*(a+b*ArcCot[c*x])/(f+g*x^2),x] + 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[Log[f_.+g_.*x_^2]*ArcTan[c_.*x_]/x_,x_Symbol] :=
  (Log[f+g*x^2]-Log[1-I*c*x]-Log[1+I*c*x])*Int[ArcTan[c*x]/x,x] + I/2*Int[Log[1-I*c*x]^2/x,x] - I/2*Int[Log[1+I*c*x]^2/x,x] /;
FreeQ[{c,f,g},x] && EqQ[g,c^2*f]


Int[Log[f_.+g_.*x_^2]*ArcCot[c_.*x_]/x_,x_Symbol] :=
  (Log[f+g*x^2]-Log[c^2*x^2]-Log[1-I/(c*x)]-Log[1+I/(c*x)])*Int[ArcCot[c*x]/x,x] + 
  Int[Log[c^2*x^2]*ArcCot[c*x]/x,x] + 
  I/2*Int[Log[1-I/(c*x)]^2/x,x] - 
  I/2*Int[Log[1+I/(c*x)]^2/x,x] /;
FreeQ[{c,f,g},x] && EqQ[g,c^2*f]


Int[Log[f_.+g_.*x_^2]*(a_+b_.*ArcTan[c_.*x_])/x_,x_Symbol] :=
  a*Int[Log[f+g*x^2]/x,x] + b*Int[Log[f+g*x^2]*ArcTan[c*x]/x,x] /;
FreeQ[{a,b,c,f,g},x]


Int[Log[f_.+g_.*x_^2]*(a_+b_.*ArcCot[c_.*x_])/x_,x_Symbol] :=
  a*Int[Log[f+g*x^2]/x,x] + b*Int[Log[f+g*x^2]*ArcCot[c*x]/x,x] /;
FreeQ[{a,b,c,f,g},x]


Int[(d_+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_])/x_,x_Symbol] :=
  d*Int[(a+b*ArcTan[c*x])/x,x] + e*Int[Log[f+g*x^2]*(a+b*ArcTan[c*x])/x,x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[(d_+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_])/x_,x_Symbol] :=
  d*Int[(a+b*ArcCot[c*x])/x,x] + e*Int[Log[f+g*x^2]*(a+b*ArcCot[c*x])/x,x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  x^(m+1)*(d+e*Log[f+g*x^2])*(a+b*ArcTan[c*x])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcTan[c*x])/(f+g*x^2),x] - 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m/2,0]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  x^(m+1)*(d+e*Log[f+g*x^2])*(a+b*ArcCot[c*x])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcCot[c*x])/(f+g*x^2),x] + 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m/2,0]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*Log[f+g*x^2]),x]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[(m+1)/2,0]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*Log[f+g*x^2]),x]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[(m+1)/2,0]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(a+b*ArcTan[c*x]),x]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && NeQ[m,-1]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(a+b*ArcCot[c*x]),x]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && NeQ[m,-1]


Int[x_*(d_.+e_.*Log[f_+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_])^2,x_Symbol] :=
  (f+g*x^2)*(d+e*Log[f+g*x^2])*(a+b*ArcTan[c*x])^2/(2*g) - 
  e*x^2*(a+b*ArcTan[c*x])^2/2 - 
  b/c*Int[(d+e*Log[f+g*x^2])*(a+b*ArcTan[c*x]),x] + 
  b*c*e*Int[x^2*(a+b*ArcTan[c*x])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[g,c^2*f]


Int[x_*(d_.+e_.*Log[f_+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_])^2,x_Symbol] :=
  (f+g*x^2)*(d+e*Log[f+g*x^2])*(a+b*ArcCot[c*x])^2/(2*g) - 
  e*x^2*(a+b*ArcCot[c*x])^2/2 + 
  b/c*Int[(d+e*Log[f+g*x^2])*(a+b*ArcCot[c*x]),x] - 
  b*c*e*Int[x^2*(a+b*ArcCot[c*x])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[g,c^2*f]


Int[u_.*(a_.+b_.*ArcTan[c_.*x_])^p_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcTan[c*x])^p,x] /;
FreeQ[{a,b,c,p},x] && (EqQ[u,1] || 
  MatchQ[u,(d_.+e_.*x)^q_./; FreeQ[{d,e,q},x]] || 
  MatchQ[u,(f_.*x)^m_.*(d_.+e_.*x)^q_./; FreeQ[{d,e,f,m,q},x]] || 
  MatchQ[u,(d_.+e_.*x^2)^q_./; FreeQ[{d,e,q},x]] || 
  MatchQ[u,(f_.*x)^m_.*(d_.+e_.*x^2)^q_./; FreeQ[{d,e,f,m,q},x]])


Int[u_.*(a_.+b_.*ArcCot[c_.*x_])^p_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcCot[c*x])^p,x] /;
FreeQ[{a,b,c,p},x] && (EqQ[u,1] || 
  MatchQ[u,(d_.+e_.*x)^q_./; FreeQ[{d,e,q},x]] || 
  MatchQ[u,(f_.*x)^m_.*(d_.+e_.*x)^q_./; FreeQ[{d,e,f,m,q},x]] || 
  MatchQ[u,(d_.+e_.*x^2)^q_./; FreeQ[{d,e,q},x]] || 
  MatchQ[u,(f_.*x)^m_.*(d_.+e_.*x^2)^q_./; FreeQ[{d,e,f,m,q},x]])


Int[ArcTan[c_.*x_^n_],x_Symbol] :=
  x*ArcTan[c*x^n] - c*n*Int[x^n/(1+c^2*x^(2*n)),x] /;
FreeQ[{c,n},x]


Int[ArcCot[c_.*x_^n_],x_Symbol] :=
  x*ArcCot[c*x^n] + c*n*Int[x^n/(1+c^2*x^(2*n)),x] /;
FreeQ[{c,n},x]


Int[(a_.+b_.*ArcTan[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+(I*b*Log[1-I*c*x^n])/2-(I*b*Log[1+I*c*x^n])/2)^p,x],x] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0] && IntegerQ[n]


Int[(a_.+b_.*ArcCot[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+(I*b*Log[1-I*x^(-n)/c])/2-(I*b*Log[1+I*x^(-n)/c])/2)^p,x],x] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0] && IntegerQ[n]


Int[(a_.+b_.*ArcTan[c_.*x_^n_])^p_./x_,x_Symbol] :=
  1/n*Subst[Int[(a+b*ArcTan[c*x])^p/x,x],x,x^n] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcCot[c_.*x_^n_])^p_./x_,x_Symbol] :=
  1/n*Subst[Int[(a+b*ArcCot[c*x])^p/x,x],x,x^n] /;
FreeQ[{a,b,c,n},x] && IGtQ[p,0]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_^n_]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcTan[c*x^n])/(d*(m+1)) - 
  b*c*n/(d*(m+1))*Int[x^(n-1)*(d*x)^(m+1)/(1+c^2*x^(2*n)),x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_^n_]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCot[c*x^n])/(d*(m+1)) + 
  b*c*n/(d*(m+1))*Int[x^(n-1)*(d*x)^(m+1)/(1+c^2*x^(2*n)),x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*(a+(I*b*Log[1-I*c*x^n])/2-(I*b*Log[1+I*c*x^n])/2)^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0] && IntegerQ[m] && IntegerQ[n]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*(a+(I*b*Log[1-I*x^(-n)/c])/2-(I*b*Log[1+I*x^(-n)/c])/2)^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0] && IntegerQ[m] && IntegerQ[n]


Int[u_.*(a_.+b_.*ArcTan[c_.*x_^n_])^p_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcTan[c*x^n])^p,x] /;
FreeQ[{a,b,c,n,p},x] && (EqQ[u,1] || MatchQ[u,(d_.*x)^m_./; FreeQ[{d,m},x]]) 


Int[u_.*(a_.+b_.*ArcCot[c_.*x_^n_])^p_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcCot[c*x^n])^p,x] /;
FreeQ[{a,b,c,n,p},x] && (EqQ[u,1] || MatchQ[u,(d_.*x)^m_./; FreeQ[{d,m},x]]) 





(* ::Subsection::Closed:: *)
(*5.2.2 u (a+b arctan(c+d x))^p*)


Int[(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcTan[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCot[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcTan[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(a+b*ArcTan[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]


Int[(a_.+b_.*ArcCot[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(a+b*ArcCot[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(f*x/d)^m*(a+b*ArcTan[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(f*x/d)^m*(a+b*ArcCot[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcTan[c+d*x])^p/(f*(m+1)) - 
  b*d*p/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcTan[c+d*x])^(p-1)/(1+(c+d*x)^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[m,-1]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
  (e+f*x)^(m+1)*(a+b*ArcCot[c+d*x])^p/(f*(m+1)) + 
  b*d*p/(f*(m+1))*Int[(e+f*x)^(m+1)*(a+b*ArcCot[c+d*x])^(p-1)/(1+(c+d*x)^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[m,-1]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcTan[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCot[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(e+f*x)^m*(a+b*ArcTan[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(e+f*x)^m*(a+b*ArcCot[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]


Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*x]/(c+d*x^n),x] -
  I/2*Int[Log[1+I*a+I*b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[(-I+a+b*x)/(a+b*x)]/(c+d*x^n),x] -
  I/2*Int[Log[(I+a+b*x)/(a+b*x)]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Unintegrable[ArcTan[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Unintegrable[ArcCot[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^q*(a+b*ArcTan[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,p,q},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^q*(a+b*ArcCot[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,p,q},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^q*(a+b*ArcTan[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,p,q},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^q*(a+b*ArcCot[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,p,q},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]





(* ::Subsection::Closed:: *)
(*5.2.3 Exponentials of inverse tangent*)


Int[E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  Int[((1-I*a*x)^((I*n+1)/2)/((1+I*a*x)^((I*n-1)/2)*Sqrt[1+a^2*x^2])),x] /;
FreeQ[a,x] && IntegerQ[(I*n-1)/2]


Int[x_^m_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  Int[x^m*((1-I*a*x)^((I*n+1)/2)/((1+I*a*x)^((I*n-1)/2)*Sqrt[1+a^2*x^2])),x] /;
FreeQ[{a,m},x] && IntegerQ[(I*n-1)/2]


Int[E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,n},x] && Not[IntegerQ[(I*n-1)/2]]


Int[x_^m_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[x^m*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[(I*n-1)/2]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1+d*x/c)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2,0] && (IntegerQ[p] || GtQ[c,0])


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[u*(c+d*x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2,0] && Not[IntegerQ[p] || GtQ[c,0]]


Int[u_.*(c_+d_./x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[c^2+a^2*d^2,0] && IntegerQ[p]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*c^p*Int[u*(1+d/(c*x))^p*(1-1/(I*a*x))^(I*n/2)/(1+1/(I*a*x))^(I*n/2),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && GtQ[c,0]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  Int[u*(c+d/x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[GtQ[c,0]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  x^p*(c+d/x)^p/(1+c*x/d)^p*Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[p]]


Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n+a*x)*E^(n*ArcTan[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[I*n]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (n-2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*c*(n^2+4*(p+1)^2)) + 
  2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && Not[IntegerQ[I*n]] && NeQ[n^2+4*(p+1)^2,0] && IntegerQ[2*p]


Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcTan[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c]


Int[(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[(1+a^2*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,p},x] && EqQ[d,a^2*c] && IntegerQ[p] && IntegerQ[(I*n+1)/2] && Not[IntegerQ[p-I*n/2]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0])


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(I*n/2)*Int[(c+d*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && IGtQ[I*n/2,0]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  1/c^(I*n/2)*Int[(c+d*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && ILtQ[I*n/2,0]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p]*Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]]


Int[x_*E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcTan[a*x])/(d*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[I*n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(2*d*(p+1)) - a*c*n/(2*d*(p+1))*Int[(c+d*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && Not[IntegerQ[I*n]] && IntegerQ[2*p]


(* Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a^2*c*(n^2+4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && NeQ[n^2+4*(p+1)^2,0] && Not[IntegerQ[I*n]] *)


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(1-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*d*n*(n^2+1)) /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && EqQ[n^2-2*(p+1),0] && Not[IntegerQ[I*n]]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*d*(n^2+4*(p+1)^2)) + 
  (n^2-2*(p+1))/(d*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && Not[IntegerQ[I*n]] && NeQ[n^2+4*(p+1)^2,0] && IntegerQ[2*p]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1+a^2*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0]) && IntegerQ[(I*n+1)/2] && Not[IntegerQ[p-I*n/2]]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0])


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(I*n/2)*Int[x^m*(c+d*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && IGtQ[I*n/2,0]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  1/c^(I*n/2)*Int[x^m*(c+d*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && ILtQ[I*n/2,0]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p]*Int[x^m*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]]


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0])


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/((1-I*a*x)^FracPart[p]*(1+I*a*x)^FracPart[p])*
    Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0]) && IntegerQ[I*n/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p]*Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && Not[IntegerQ[I*n/2]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[c-a^2*d,0] && IntegerQ[p]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-I/(a*x))^p*(1+I/(a*x))^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c-a^2*d,0] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && GtQ[c,0]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/((1-I*a*x)^p*(1+I*a*x)^p)*Int[u/x^(2*p)*(1-I*a*x)^p*(1+I*a*x)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d,0] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[GtQ[c,0]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/(1+a^2*x^2)^p*Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d,0] && Not[IntegerQ[p]] && Not[IntegerQ[I*n/2]]


Int[E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,n},x]


Int[x_^m_*E^(n_*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(I^m*n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/(I*n))*(1-I*a*c-(1+I*a*c)*x^(2/(I*n)))^m/(1+x^(2/(I*n)))^(m+2),x],x,
      (1-I*c*(a+b*x))^(I*n/2)/(1+I*c*(a+b*x))^(I*n/2)] /;
FreeQ[{a,b,c},x] && ILtQ[m,0] && LtQ[-1,I*n,1]


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(d+e*x)^m*(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
  (c/(1+a^2))^p*Int[u*(1-I*a-I*b*x)^(p+I*n/2)*(1+I*a+I*b*x)^(p-I*n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d,2*a*e] && EqQ[b^2*c-e(1+a^2),0] && (IntegerQ[p] || GtQ[c/(1+a^2),0])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p*Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d,2*a*e] && EqQ[b^2*c-e(1+a^2),0] && Not[IntegerQ[p] || GtQ[c/(1+a^2),0]]


Int[u_.*E^(n_.*ArcTan[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcCot[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  (-1)^(I*n/2)*Int[u*E^(-n*ArcTan[a*x]),x] /;
FreeQ[a,x] && IntegerQ[I*n/2]


Int[E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^2*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
FreeQ[a,x] && IntegerQ[(I*n-1)/2]


Int[x_^m_.*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^(m+2)*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
FreeQ[a,x] && IntegerQ[(I*n-1)/2] && IntegerQ[m]


Int[E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[I*n]]


Int[x_^m_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[I*n]] && IntegerQ[m]


Int[x_^m_*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  -x^m*(1/x)^m*Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^(m+2)*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
FreeQ[{a,m},x] && IntegerQ[(I*n-1)/2] && Not[IntegerQ[m]]


Int[x_^m_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[m]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c^2+d^2,0] && Not[IntegerQ[I*n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(x^p*(1+c/(d*x))^p)*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2,0] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]


Int[(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0])


Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && IntegerQ[m]


Int[(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || GtQ[c,0]]


Int[x_^m_*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[u*(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || GtQ[c,0]]


Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  -E^(n*ArcCot[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c]


Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(n-a*x)*E^(n*ArcCot[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[(I*n-1)/2]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -(n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a*c*(n^2+4*(p+1)^2)) + 
  2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && NeQ[p,-3/2] && NeQ[n^2+4*(p+1)^2,0] && 
  Not[IntegerQ[p] && IntegerQ[I*n/2]] && Not[Not[IntegerQ[p]] && IntegerQ[(I*n-1)/2]]


Int[x_*E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1+a*n*x)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[(I*n-1)/2]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (2*(p+1)-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+4*(p+1)^2)) + 
  n*(2*p+3)/(a*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LeQ[p,-1] && NeQ[p,-3/2] && NeQ[n^2+4*(p+1)^2,0] && 
  Not[IntegerQ[p] && IntegerQ[I*n/2]] && Not[Not[IntegerQ[p]] && IntegerQ[(I*n-1)/2]]


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*n^2*(n^2+1)) /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && EqQ[n^2-2*(p+1),0] && NeQ[n^2+1,0]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*(n^2+4*(p+1)^2)) + 
  (n^2-2*(p+1))/(a^2*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LeQ[p,-1] && NeQ[n^2-2*(p+1),0] && NeQ[n^2+4*(p+1)^2,0] && 
  Not[IntegerQ[p] && IntegerQ[I*n/2]] && Not[Not[IntegerQ[p]] && IntegerQ[(I*n-1)/2]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p/a^(m+1)*Subst[Int[E^(n*x)*Cot[x]^(m+2*(p+1))/Cos[x]^(2*(p+1)),x],x,ArcCot[a*x]] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && IntegerQ[m] && LeQ[3,m,-2(p+1)] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[I*n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(x^(2*p)*(1+1/(a^2*x^2))^p)*Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  c^p/(I*a)^(2*p)*Int[u/x^(2*p)*(-1+I*a*x)^(p-I*n/2)*(1+I*a*x)^(p+I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && IntegersQ[2*p,p+I*n/2]


Int[(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^2,x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[2*p] && IntegerQ[p+I*n/2]]


Int[x_^m_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[2*p] && IntegerQ[p+I*n/2]] && 
  IntegerQ[m]


Int[x_^m_*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[2*p] && IntegerQ[p+I*n/2]] && 
  Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x^2)^p/(1+1/(a^2*x^2))^p*Int[u*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || GtQ[c,0]]


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
FreeQ[{a,b,c},x] && ILtQ[m,0] && LtQ[-1,I*n,1]


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (I*c*(a+b*x))^(I*n/2)*(1+1/(I*c*(a+b*x)))^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2)*
    Int[(d+e*x)^m*(1+I*a*c+I*b*c*x)^(I*n/2)/(-1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[I*n/2]]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
  (c/(1+a^2))^p*((I*a+I*b*x)/(1+I*a+I*b*x))^(I*n/2)*((1+I*a+I*b*x)/(I*a+I*b*x))^(I*n/2)*
    ((1-I*a-I*b*x)^(I*n/2)/(-1+I*a+I*b*x)^(I*n/2))*
    Int[u*(1-I*a-I*b*x)^(p-I*n/2)*(1+I*a+I*b*x)^(p+I*n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && EqQ[b*d-2*a*e,0] && EqQ[b^2*c-e(1+a^2),0] && (IntegerQ[p] || GtQ[c/(1+a^2),0])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p*Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && EqQ[b*d-2*a*e,0] && EqQ[b^2*c-e(1+a^2),0] && Not[IntegerQ[p] || GtQ[c/(1+a^2),0]]


Int[u_.*E^(n_.*ArcCot[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcTan[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*5.2.4 Miscellaneous inverse tangent*)
(**)


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


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
  x*ArcTan[(c*x)/Sqrt[a+b*x^2]] - c*Int[x/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c},x] && EqQ[b+c^2,0]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
  x*ArcCot[(c*x)/Sqrt[a+b*x^2]] + c*Int[x/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c},x] && EqQ[b+c^2,0]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]/x_,x_Symbol] :=
  ArcTan[c*x/Sqrt[a+b*x^2]]*Log[x] - c*Int[Log[x]/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c},x] && EqQ[b+c^2,0]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]/x_,x_Symbol] :=
  ArcCot[c*x/Sqrt[a+b*x^2]]*Log[x] + c*Int[Log[x]/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c},x] && EqQ[b+c^2,0]


Int[(d_.*x_)^m_.*ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
  (d*x)^(m+1)*ArcTan[(c*x)/Sqrt[a+b*x^2]]/(d*(m+1)) - c/(d*(m+1))*Int[(d*x)^(m+1)/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[b+c^2,0] && NeQ[m,-1]


Int[(d_.*x_)^m_.*ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
  (d*x)^(m+1)*ArcCot[(c*x)/Sqrt[a+b*x^2]]/(d*(m+1)) + c/(d*(m+1))*Int[(d*x)^(m+1)/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[b+c^2,0] && NeQ[m,-1]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  1/c*Log[ArcTan[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && EqQ[b+c^2,0]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  -1/c*Log[ArcCot[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && EqQ[b+c^2,0]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  ArcTan[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && EqQ[b+c^2,0] && NeQ[m,-1]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  -ArcCot[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && EqQ[b+c^2,0] && NeQ[m,-1]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcTan[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b+c^2,0] && EqQ[b*d-a*e,0]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcCot[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b+c^2,0] && EqQ[b*d-a*e,0]


Int[u_.*ArcTan[v_+s_.*Sqrt[w_]],x_Symbol] :=
  Pi*s/4*Int[u,x] + 1/2*Int[u*ArcTan[v],x] /;
EqQ[s^2,1] && EqQ[w,v^2+1]


Int[u_.*ArcCot[v_+s_.*Sqrt[w_]],x_Symbol] :=
  Pi*s/4*Int[u,x] - 1/2*Int[u*ArcTan[v],x] /;
EqQ[s^2,1] && EqQ[w,v^2+1]


If[$LoadShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcTan[a+b*x]]/(1+(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Tan[x]/b,x],x],x,ArcTan[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp]]] /;
 Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcTan] && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2,0]] /;
SimplifyFlag && QuadraticQ[v,x] && ILtQ[n,0] && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp] /;
 Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcTan] && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2,0]] /;
QuadraticQ[v,x] && ILtQ[n,0] && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


If[$LoadShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcCot[a+b*x]]/(1+(a+b*x)^2),x]",
		   "-Subst[Int[f[-a/b+Cot[x]/b,x],x],x,ArcCot[a+b*x]]/b",Hold[
  -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp]]] /;
 Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcCot] && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2,0]] /;
SimplifyFlag && QuadraticQ[v,x] && ILtQ[n,0] && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp] /;
 Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcCot] && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2,0]] /;
QuadraticQ[v,x] && ILtQ[n,0] && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


Int[ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tan[a+b*x]] - 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c+I*d)^2,-1]


Int[ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tan[a+b*x]] + 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c+I*d)^2,-1]


Int[ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Cot[a+b*x]] - 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-I*d)^2,-1]


Int[ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Cot[a+b*x]] + 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-I*d)^2,-1]


Int[ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tan[a+b*x]] - 
  b*(1+I*c+d)*Int[x*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(1-I*c-d)*Int[x*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2,-1]


Int[ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tan[a+b*x]] + 
  b*(1+I*c+d)*Int[x*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(1-I*c-d)*Int[x*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2,-1]


Int[ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Cot[a+b*x]] + 
  b*(1+I*c-d)*Int[x*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(1-I*c+d)*Int[x*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2,-1]


Int[ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Cot[a+b*x]] - 
  b*(1+I*c-d)*Int[x*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(1-I*c+d)*Int[x*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-I*d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Tan[a+b*x]]/(f*(m+1)) - 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c+I*d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Tan[a+b*x]]/(f*(m+1)) + 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c+I*d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Cot[a+b*x]]/(f*(m+1)) - 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-I*d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Cot[a+b*x]]/(f*(m+1)) + 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-I*d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Tan[a+b*x]]/(f*(m+1)) - 
  b*(1+I*c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(1-I*c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c+I*d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Tan[a+b*x]]/(f*(m+1)) + 
  b*(1+I*c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(1-I*c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c+I*d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Cot[a+b*x]]/(f*(m+1)) + 
  b*(1+I*c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(1-I*c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-I*d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Cot[a+b*x]]/(f*(m+1)) - 
  b*(1+I*c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(1-I*c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-I*d)^2,-1]


Int[ArcTan[Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[Tanh[a+b*x]] - b*Int[x*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcCot[Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[Tanh[a+b*x]] + b*Int[x*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcTan[Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[Coth[a+b*x]] + b*Int[x*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcCot[Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[Coth[a+b*x]] - b*Int[x*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[(e_.+f_.*x_)^m_.*ArcTan[Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[Tanh[a+b*x]]/(f*(m+1)) - b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*ArcCot[Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[Tanh[a+b*x]]/(f*(m+1)) + b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*ArcTan[Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[Coth[a+b*x]]/(f*(m+1)) + b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*ArcCot[Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[Coth[a+b*x]]/(f*(m+1)) - b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m,0]


Int[ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tanh[a+b*x]] - 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,-1]


Int[ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tanh[a+b*x]] + 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,-1]


Int[ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Coth[a+b*x]] - 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,-1]


Int[ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Coth[a+b*x]] + 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,-1]


Int[ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tanh[a+b*x]] + 
  I*b*(I-c-d)*Int[x*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c+d)*Int[x*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,-1]


Int[ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tanh[a+b*x]] - 
  I*b*(I-c-d)*Int[x*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c+d)*Int[x*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,-1]


Int[ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Coth[a+b*x]] - 
  I*b*(I-c-d)*Int[x*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c+d)*Int[x*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,-1]


Int[ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Coth[a+b*x]] + 
  I*b*(I-c-d)*Int[x*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c+d)*Int[x*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Tanh[a+b*x]]/(f*(m+1)) - 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Tanh[a+b*x]]/(f*(m+1)) + 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Coth[a+b*x]]/(f*(m+1)) - 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Coth[a+b*x]]/(f*(m+1)) + 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Tanh[a+b*x]]/(f*(m+1)) + 
  I*b*(I-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Tanh[a+b*x]]/(f*(m+1)) - 
  I*b*(I-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Coth[a+b*x]]/(f*(m+1)) - 
  I*b*(I-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,-1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Coth[a+b*x]]/(f*(m+1)) + 
  I*b*(I-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,-1]


Int[ArcTan[u_],x_Symbol] :=
  x*ArcTan[u] -
  Int[SimplifyIntegrand[x*D[u,x]/(1+u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[ArcCot[u_],x_Symbol] :=
  x*ArcCot[u] +
  Int[SimplifyIntegrand[x*D[u,x]/(1+u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcTan[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcTan[u])/(d*(m+1)) -
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1+u^2),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCot[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCot[u])/(d*(m+1)) +
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1+u^2),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[v_*(a_.+b_.*ArcTan[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcTan[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcTan[u]),x]]


Int[v_*(a_.+b_.*ArcCot[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCot[u]),w,x] + b*Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcCot[u]),x]]


Int[ArcTan[v_]*Log[w_]/(a_.+b_.*x_),x_Symbol] :=
  I/2*Int[Log[1-I*v]*Log[w]/(a+b*x),x] - I/2*Int[Log[1+I*v]*Log[w]/(a+b*x),x] /;
FreeQ[{a,b},x] && LinearQ[v,x] && LinearQ[w,x] && EqQ[Simplify[D[v/(a+b*x),x]],0] && EqQ[Simplify[D[w/(a+b*x),x]],0]


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
  With[{z=IntHide[u,x]},  
  Dist[ArcTan[v]*Log[w],z,x] - 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[z*ArcTan[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*ArcCot[v_]*Log[w_],x_Symbol] :=
  With[{z=IntHide[u,x]},  
  Dist[ArcCot[v]*Log[w],z,x] + 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[z*ArcCot[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]





(* ::Subsection::Closed:: *)
(*5.3.1 u (a+b arcsec(c x))^n*)


Int[ArcSec[c_.*x_],x_Symbol] :=
  x*ArcSec[c*x] - 1/c*Int[1/(x*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[c,x]


Int[ArcCsc[c_.*x_],x_Symbol] :=
  x*ArcCsc[c*x] + 1/c*Int[1/(x*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[c,x]


Int[(a_.+b_.*ArcSec[c_.*x_])^n_,x_Symbol] :=
  1/c*Subst[Int[(a+b*x)^n*Sec[x]*Tan[x],x],x,ArcSec[c*x]] /;
FreeQ[{a,b,c,n},x] && IGtQ[n,0]


Int[(a_.+b_.*ArcCsc[c_.*x_])^n_,x_Symbol] :=
  -1/c*Subst[Int[(a+b*x)^n*Csc[x]*Cot[x],x],x,ArcCsc[c*x]] /;
FreeQ[{a,b,c,n},x] && IGtQ[n,0]


Int[(a_.+b_.*ArcSec[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcCos[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcCsc[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcSin[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcSec[c*x])/(d*(m+1)) - 
  b*d/(c*(m+1))*Int[(d*x)^(m-1)/Sqrt[1-1/(c^2*x^2)],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCsc[c*x])/(d*(m+1)) + 
  b*d/(c*(m+1))*Int[(d*x)^(m-1)/Sqrt[1-1/(c^2*x^2)],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]


Int[x_^m_.*(a_.+b_.*ArcSec[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Sec[x]^(m+1)*Tan[x],x],x,ArcSec[c*x]] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && IntegerQ[m] && (GtQ[n,0] || LtQ[m,-1])


Int[x_^m_.*(a_.+b_.*ArcCsc[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Csc[x]^(m+1)*Cot[x],x],x,ArcCsc[c*x]] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && IntegerQ[m] && (GtQ[n,0] || LtQ[m,-1])


Int[(a_.+b_.*ArcSec[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  (a+b*ArcSec[c*x])*Log[1+(e-Sqrt[-c^2*d^2+e^2])*E^(I*ArcSec[c*x])/(c*d)]/e + 
  (a+b*ArcSec[c*x])*Log[1+(e+Sqrt[-c^2*d^2+e^2])*E^(I*ArcSec[c*x])/(c*d)]/e - 
  (a+b*ArcSec[c*x])*Log[1+E^(2*I*ArcSec[c*x])]/e - 
  b/(c*e)*Int[Log[1+(e-Sqrt[-c^2*d^2+e^2])*E^(I*ArcSec[c*x])/(c*d)]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] - 
  b/(c*e)*Int[Log[1+(e+Sqrt[-c^2*d^2+e^2])*E^(I*ArcSec[c*x])/(c*d)]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] + 
  b/(c*e)*Int[Log[1+E^(2*I*ArcSec[c*x])]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(a_.+b_.*ArcCsc[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  (a+b*ArcCsc[c*x])*Log[1-I*(e-Sqrt[-c^2*d^2+e^2])*E^(I*ArcCsc[c*x])/(c*d)]/e + 
  (a+b*ArcCsc[c*x])*Log[1-I*(e+Sqrt[-c^2*d^2+e^2])*E^(I*ArcCsc[c*x])/(c*d)]/e - 
  (a+b*ArcCsc[c*x])*Log[1-E^(2*I*ArcCsc[c*x])]/e + 
  b/(c*e)*Int[Log[1-I*(e-Sqrt[-c^2*d^2+e^2])*E^(I*ArcCsc[c*x])/(c*d)]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] + 
  b/(c*e)*Int[Log[1-I*(e+Sqrt[-c^2*d^2+e^2])*E^(I*ArcCsc[c*x])/(c*d)]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] - 
  b/(c*e)*Int[Log[1-E^(2*I*ArcCsc[c*x])]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcSec[c*x])/(e*(m+1)) - 
  b/(c*e*(m+1))*Int[(d+e*x)^(m+1)/(x^2*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCsc[c*x])/(e*(m+1)) + 
  b/(c*e*(m+1))*Int[(d+e*x)^(m+1)/(x^2*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcSec[c*x]),u,x] - b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcCsc[c*x]),u,x] + b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSec[c*x])/(2*e*(p+1)) - 
  b*c*x/(2*e*(p+1)*Sqrt[c^2*x^2])*Int[(d+e*x^2)^(p+1)/(x*Sqrt[c^2*x^2-1]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCsc[c*x])/(2*e*(p+1)) + 
  b*c*x/(2*e*(p+1)*Sqrt[c^2*x^2])*Int[(d+e*x^2)^(p+1)/(x*Sqrt[c^2*x^2-1]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcSec[c*x]),u,x] - b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && (
  IGtQ[p,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*p+3,0]] || 
  IGtQ[(m+1)/2,0] && Not[ILtQ[p,0] && GtQ[m+2*p+3,0]] || 
  ILtQ[(m+2*p+1)/2,0] && Not[ILtQ[(m-1)/2,0]])


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcCsc[c*x]),u,x] + b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && (
  IGtQ[p,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*p+3,0]] || 
  IGtQ[(m+1)/2,0] && Not[ILtQ[p,0] && GtQ[m+2*p+3,0]] || 
  ILtQ[(m+2*p+1)/2,0] && Not[ILtQ[(m-1)/2,0]])


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[m] && IntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[m] && IntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]


Int[u_*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[(a+b*ArcSec[c*x]),v,x] - 
  b/c*Int[SimplifyIntegrand[v/(x^2*Sqrt[1-1/(c^2*x^2)]),x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[u_*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[(a+b*ArcCsc[c*x]),v,x] + 
  b/c*Int[SimplifyIntegrand[v/(x^2*Sqrt[1-1/(c^2*x^2)]),x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[u_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcSec[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  Unintegrable[u*(a+b*ArcCsc[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*5.3.2 Miscellaneous inverse secant*)


Int[ArcSec[c_+d_.*x_],x_Symbol] :=
  (c+d*x)*ArcSec[c+d*x]/d - 
  Int[1/((c+d*x)*Sqrt[1-1/(c+d*x)^2]),x] /;
FreeQ[{c,d},x]


Int[ArcCsc[c_+d_.*x_],x_Symbol] :=
  (c+d*x)*ArcCsc[c+d*x]/d + 
  Int[1/((c+d*x)*Sqrt[1-1/(c+d*x)^2]),x] /;
FreeQ[{c,d},x]


Int[(a_.+b_.*ArcSec[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcSec[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcCsc[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCsc[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && IGtQ[p,0]


Int[(a_.+b_.*ArcSec[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(a+b*ArcSec[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]


Int[(a_.+b_.*ArcCsc[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(a+b*ArcCsc[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSec[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(f*x/d)^m*(a+b*ArcSec[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsc[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[(f*x/d)^m*(a+b*ArcCsc[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSec[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d^(m+1)*Subst[Int[(a+b*x)^p*Sec[x]*Tan[x]*(d*e-c*f+f*Sec[x])^m,x],x,ArcSec[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsc[c_+d_.*x_])^p_.,x_Symbol] :=
  -1/d^(m+1)*Subst[Int[(a+b*x)^p*Csc[x]*Cot[x]*(d*e-c*f+f*Csc[x])^m,x],x,ArcCsc[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSec[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSec[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsc[c_+d_.*x_])^p_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCsc[x])^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSec[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(e+f*x)^m*(a+b*ArcSec[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsc[c_+d_.*x_])^p_,x_Symbol] :=
  Unintegrable[(e+f*x)^m*(a+b*ArcCsc[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]


Int[u_.*ArcSec[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCos[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCsc[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSin[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*f_^(c_.*ArcSec[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[ReplaceAll[u,x->-a/b+Sec[x]/b]*f^(c*x^n)*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,c,f},x] && IGtQ[n,0]


Int[u_.*f_^(c_.*ArcCsc[a_.+b_.*x_]^n_.),x_Symbol] :=
  -1/b*Subst[Int[ReplaceAll[u,x->-a/b+Csc[x]/b]*f^(c*x^n)*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,c,f},x] && IGtQ[n,0]


Int[ArcSec[u_],x_Symbol] :=
  x*ArcSec[u] -
  u/Sqrt[u^2]*Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCsc[u_],x_Symbol] :=
  x*ArcCsc[u] +
  u/Sqrt[u^2]*Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSec[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcSec[u])/(d*(m+1)) -
  b*u/(d*(m+1)*Sqrt[u^2])*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCsc[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCsc[u])/(d*(m+1)) +
  b*u/(d*(m+1)*Sqrt[u^2])*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSec[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcSec[u]),w,x] - b*u/Sqrt[u^2]*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCsc[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCsc[u]),w,x] + b*u/Sqrt[u^2]*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]



