(* ::Package:: *)

(* ::Section:: *)
(*Inverse Trig Function Rules*)


(* ::Subsection::Closed:: *)
(*u (a+b arcsin(c x))^n*)


Int[(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcSin[c*x])^n - 
  b*c*n*Int[x*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcCos[c*x])^n + 
  b*c*n*Int[x*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) + 
  c/(b*(n+1))*Int[x*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  c/(b*(n+1))*Int[x*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  1/(b*c)*Subst[Int[x^n*Cos[a/b-x/b],x],x,a+b*ArcSin[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  1/(b*c)*Subst[Int[x^n*Sin[a/b-x/b],x],x,a+b*ArcCos[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcSin[c*x])^n/(e*(m+1)) - 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && RationalQ[n] && n>0 && NonzeroQ[m+1]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCos[c*x])^n/(e*(m+1)) + 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && RationalQ[n] && n>0 && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1),Sin[x]^(m-1)*(m-(m+1)*Sin[x]^2),x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -2<=n<-1 && PositiveIntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -x^m*Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1),Cos[x]^(m-1)*(m-(m+1)*Cos[x]^2),x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -2<=n<-1 && PositiveIntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] + 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-2 && PositiveIntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -x^m*Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] - 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-2 && PositiveIntegerQ[m]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[n] && n<-1 && PositiveIntegerQ[m]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[n] && n<-1 && PositiveIntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]*(c*d+e*Sin[x])^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[m] && (m>0 || PositiveIntegerQ[n])


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]*(c*d+e*Cos[x])^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[m] && (m>0 || PositiveIntegerQ[n])


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (PositiveIntegerQ[p] || NonzeroQ[a])


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (PositiveIntegerQ[p] || NonzeroQ[a])


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[(d*f+e*g*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && IntegerQ[p]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[(d*f+e*g*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && IntegerQ[p]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[d*f+e*g*x^2]*Int[(d*f+e*g*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && PositiveIntegerQ[p+1/2]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[d*f+e*g*x^2]*Int[(d*f+e*g*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && PositiveIntegerQ[p+1/2]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[(d*f+e*g*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && NegativeIntegerQ[p-1/2]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[(d*f+e*g*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && NegativeIntegerQ[p-1/2]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x)^p*(f+g*x)^p,x]]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[p]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x)^p*(f+g*x)^p,x]]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[p]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x)^p*(f+g*x)^p,x]]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[p+1/2]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x)^p*(f+g*x)^p,x]]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[p+1/2]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(f+g*x)^p*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[p]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(f+g*x)^p*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[p]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(f+g*x)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(f+g*x)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(b*c*Sqrt[d])*Subst[Int[x^n,x],x,a+b*ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(b*c*Sqrt[d])*Subst[Int[x^n,x],x,a+b*ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(2*p+1) - 
  b*c*n*Sqrt[d]/(2*p+1)*Int[x*(d+e*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(2*p+1) + 
  b*c*n*Sqrt[d]/(2*p+1)*Int[x*(d+e*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p>0


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/(c*d)*Subst[Int[(a+b*x)^n*Sec[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -1/(c*d)*Subst[Int[(a+b*x)^n*Csc[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcSin[c*x])^n/(d*Sqrt[d+e*x^2]) - b*c*n/Sqrt[d]*Int[x*(a+b*ArcSin[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcCos[c*x])^n/(d*Sqrt[d+e*x^2]) + b*c*n/Sqrt[d]*Int[x*(a+b*ArcCos[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && RationalQ[n] && n>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*(p+1)) + 
  b*c*n/(2*Sqrt[d]*(p+1))*Int[x*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p<-1 && p!=-2/3


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*(p+1)) - 
  b*c*n/(2*Sqrt[d]*(p+1))*Int[x*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p<-1 && p!=-2/3


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  e*(2*p+1)/(b*c*Sqrt[d]*(n+1))*Int[x*(d+e*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n<-1 && p!=-1/2


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  e*(2*p+1)/(b*c*Sqrt[d]*(n+1))*Int[x*(d+e*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n<-1 && p!=-1/2


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^p/c*Subst[Int[(a+b*x)^n*Cos[x]^(2*p+1),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[2*p] && PositiveQ[d]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c*Subst[Int[(a+b*x)^n*Sin[x]^(2*p+1),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[2*p] && PositiveQ[d]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^p*Int[(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p] && Not[PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^p*Int[(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p] && Not[PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && Not[PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && Not[PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && PositiveIntegerQ[p]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && PositiveIntegerQ[p]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(Sqrt[d]-Sqrt[-e]*x)^p*(Sqrt[d]+Sqrt[-e]*x)^p*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NegativeIntegerQ[p] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(Sqrt[d]-Sqrt[-e]*x)^p*(Sqrt[d]+Sqrt[-e]*x)^p*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NegativeIntegerQ[p] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[d*f+e*g*x^2]*Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && PositiveIntegerQ[p+1/2]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[d*f+e*g*x^2]*Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && PositiveIntegerQ[p+1/2]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && NegativeIntegerQ[p-1/2]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && NegativeIntegerQ[p-1/2]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])/(2*e*(p+1)) - 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])/(2*e*(p+1)) + 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) + 
  b*n/(2*c*Sqrt[d]*(p+1))*Int[(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p!=-1


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  b*n/(2*c*Sqrt[d]*(p+1))*Int[(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(m+1) - 
  b*c*Sqrt[d]*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] - 
  2*e*p/(m+1)*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p>0 && m<-1


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(m+1) + 
  b*c*Sqrt[d]*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] - 
  2*e*p/(m+1)*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p>0 && m<-1


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(m+2*p+1) - 
  b*c*n*Sqrt[d]/(m+2*p+1)*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] + 
  2*d*p/(m+2*p+1)*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p>0 && m+2*p+1!=0


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(m+2*p+1) + 
  b*c*n*Sqrt[d]/(m+2*p+1)*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] + 
  2*d*p/(m+2*p+1)*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p>0 && m+2*p+1!=0


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*(m+1)) - 
  b*c*n/(Sqrt[d]*(m+1))*Int[x^(m+1)*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<0 && m!=-1 && m+2*p+3==0


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*(m+1)) + 
  b*c*n/(Sqrt[d]*(m+1))*Int[x^(m+1)*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<0 && m!=-1 && m+2*p+3==0


Int[x_^m_*(a_.+b_.*ArcSin[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*(a+b*ArcSin[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2]/(Sqrt[d]*(m+1)) - 
  b*c*x^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2]/(Sqrt[d]*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && Not[IntegerQ[m]]


Int[x_^m_*(a_.+b_.*ArcCos[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*(a+b*ArcCos[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2]/(Sqrt[d]*(m+1)) + 
  b*c*x^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2]/(Sqrt[d]*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && Not[IntegerQ[m]]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/(c^(m+1)*d)*Subst[Int[(a+b*x)^n*Sin[x]^m*Sec[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[n] && IntegerQ[m] && m^2==1


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -1/(c^(m+1)*d)*Subst[Int[(a+b*x)^n*Cos[x]^m*Csc[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[n] && IntegerQ[m] && m^2==1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(e*(m+2*p+1)) - 
  b*c*Sqrt[d]*n/(e*(m+2*p+1))*Int[x^(m-1)*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] + 
  (m-1)/(c^2*(m+2*p+1))*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && -1<=p<0 && m>1 && NonzeroQ[m+2*p+1]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(e*(m+2*p+1)) + 
  b*c*Sqrt[d]*n/(e*(m+2*p+1))*Int[x^(m-1)*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] + 
  (m-1)/(c^2*(m+2*p+1))*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && -1<=p<0 && m>1 && NonzeroQ[m+2*p+1]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) + 
  b*n/(2*c*Sqrt[d]*(p+1))*Int[x^(m-1)*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] - 
  (m-1)/(2*e*(p+1))*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<-1 && m>1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  b*n/(2*c*Sqrt[d]*(p+1))*Int[x^(m-1)*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] - 
  (m-1)/(2*e*(p+1))*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<-1 && m>1


Int[ArcSin[c_.*x_]/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2*I*ArcSin[c*x]*ArcTan[c*x-I*Sqrt[1-c^2*x^2]]/Sqrt[d] + 
  I*PolyLog[2,-I*(c*x)-Sqrt[1-c^2*x^2]]/Sqrt[d] - 
  I*PolyLog[2,I*(c*x)+Sqrt[1-c^2*x^2]]/Sqrt[d] /;
FreeQ[{c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[ArcCos[c_.*x_]/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  2*I*ArcCos[c*x]*ArcTan[c*x+I*Sqrt[1-c^2*x^2]]/Sqrt[d] - 
  I*PolyLog[2,-I*(c*x)+Sqrt[1-c^2*x^2]]/Sqrt[d] + 
  I*PolyLog[2,I*(c*x)-Sqrt[1-c^2*x^2]]/Sqrt[d] /;
FreeQ[{c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(a_+b_.*ArcSin[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  a*Int[1/(x*Sqrt[d+e*x^2]),x] + 
  b*Int[ArcSin[c*x]/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(a_+b_.*ArcCos[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  a*Int[1/(x*Sqrt[d+e*x^2]),x] + 
  b*Int[ArcCos[c*x]/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_./x_,x_Symbol] :=
  c^2*Int[x*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] + 
  1/d*Int[(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/x,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p<-1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_./x_,x_Symbol] :=
  c^2*Int[x*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] + 
  1/d*Int[(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/x,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p<-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*(m+1)) - 
  b*c*n/(Sqrt[d]*(m+1))*Int[x^(m+1)*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] + 
  c^2*(m+2*p+3)/(m+1)*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<0 && m<-1 && m+2*p+3!=0


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*(m+1)) + 
  b*c*n/(Sqrt[d]*(m+1))*Int[x^(m+1)*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] + 
  c^2*(m+2*p+3)/(m+1)*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<0 && m<-1 && m+2*p+3!=0


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^m*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && RationalQ[n] && n<-1


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -x^m*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  d*m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n<-1 && m+2*p+1==0


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -x^m*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  d*m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(d+e*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n<-1 && m+2*p+1==0


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  d*m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] - 
  e*(m+2*p+1)/(b*c*Sqrt[d]*(n+1))*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -x^m*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  d*m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(d+e*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] + 
  e*(m+2*p+1)/(b*c*Sqrt[d]*(n+1))*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] - 
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[p+1/2] && PositiveQ[d] && NegativeIntegerQ[(m-1)/2]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[p+1/2] && PositiveQ[d] && NegativeIntegerQ[(m-1)/2]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*Sin[x]^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && IntegerQ[m] && (m>0 || PositiveIntegerQ[n])


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*Cos[x]^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && IntegerQ[m] && (m>0 || PositiveIntegerQ[n])


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]^m*Cos[x]^(2*p+1),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[2*p] && PositiveQ[d] && PositiveIntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]^m*Sin[x]^(2*p+1),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[2*p] && PositiveQ[d] && PositiveIntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n/Sqrt[d+e*x^2],x^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && PositiveQ[d] && Not[PositiveIntegerQ[(m+1)/2]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n/Sqrt[d+e*x^2],x^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && PositiveQ[d] && Not[PositiveIntegerQ[(m+1)/2]]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^p*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p] && Not[PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^p*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p] && Not[PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && Not[PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && Not[PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(h_.+i_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_./(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[(h+i*x)^m*(a+b*ArcSin[c*x])^n/Sqrt[d*f+e*g*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n},x] && ZeroQ[e*f+d*g]


Int[(h_.+i_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_./(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[(h+i*x)^m*(a+b*ArcCos[c*x])^n/Sqrt[d*f+e*g*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n},x] && ZeroQ[e*f+d*g]


Int[(i_*x_)^m_*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (i*x)^m/x^m*Int[x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,i,m,n,p},x]


Int[(i_*x_)^m_*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (i*x)^m/x^m*Int[x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,i,m,n,p},x]


Int[(h_.+i_.*x_)^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(h+i*x)^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n,p},x]


Int[(h_.+i_.*x_)^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(h+i*x)^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n,p},x]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f+g*x)^m*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && RationalQ[n] && n<-1


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -(f+g*x)^m*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && RationalQ[n] && n<-1


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*(c*f+g*Sin[x])^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && IntegerQ[m]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*(c*f+g*Cos[x])^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[c^2*d+e] && PositiveQ[d] && IntegerQ[m]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(f+g*x)^m*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[c^2*d+e] && Not[PositiveQ[d]]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(f+g*x)^m*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[c^2*d+e] && Not[PositiveQ[d]]


Int[(g_*x_)^m_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (g*x)^m/x^m*Int[x^m*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,g,m,n,p},x]


Int[(g_*x_)^m_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (g*x)^m/x^m*Int[x^m*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,g,m,n,p},x]


Int[(f_.+g_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(f+g*x)^m*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[(f_.+g_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(f+g*x)^m*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


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
FreeQ[{a,b,c,d,A,B,C,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


(* ::Subsection::Closed:: *)
(*u (a+b arctan(c x))^n*)


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^n -
  b*c*n*Int[x*(a+b*ArcTan[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcCot[c*x])^n +
  b*c*n*Int[x*(a+b*ArcCot[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTan[c*x])^n*Log[2*d/(d+e*x)]/e +
  b*c*n/e*Int[(a+b*ArcTan[c*x])^(n-1)*Log[2*d/(d+e*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2+e^2] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCot[c*x])^n*Log[2*d/(d+e*x)]/e -
  b*c*n/e*Int[(a+b*ArcCot[c*x])^(n-1)*Log[2*d/(d+e*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2+e^2] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcTan[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  a/e*Log[RemoveContent[d+e*x,x]] + I*b/2*Int[Log[1-I*c*x]/(d+e*x),x] - I*b/2*Int[Log[1+I*c*x]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(a_.+b_.*ArcCot[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  a/e*Log[RemoveContent[d+e*x,x]] + I*b/2*Int[Log[1-I/(c*x)]/(d+e*x),x] - I*b/2*Int[Log[1+I/(c*x)]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  (d+e*x)^(p+1)*(a+b*ArcTan[c*x])/(e*(p+1)) - 
  b*c/(e*(p+1))*Int[(d+e*x)^(p+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  (d+e*x)^(p+1)*(a+b*ArcCot[c*x])/(e*(p+1)) + 
  b*c/(e*(p+1))*Int[(d+e*x)^(p+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_/x_,x_Symbol] :=
  2*(a+b*ArcTan[c*x])^n*ArcTanh[1-2*I/(I-c*x)] -
  2*b*c*n*Int[(a+b*ArcTan[c*x])^(n-1)*ArcTanh[1-2*I/(I-c*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[(a_.+b_.*ArcCot[c_.*x_])^n_/x_,x_Symbol] :=
  2*(a+b*ArcCot[c*x])^n*ArcCoth[1-2*I/(I-c*x)] +
  2*b*c*n*Int[(a+b*ArcCot[c*x])^(n-1)*ArcCoth[1-2*I/(I-c*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcTan[c*x])^n/(m+1) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcTan[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,m},x] && IntegerQ[n] && n>1 && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcCot[c*x])^n/(m+1) + 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCot[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,m},x] && IntegerQ[n] && n>1 && NonzeroQ[m+1]


Int[(d_+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(a+b*ArcTan[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[n,p]


Int[(d_+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(a+b*ArcCot[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[n,p]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/e*Int[x^(m-1)*(a+b*ArcTan[c*x])^n,x] -
  d/e*Int[x^(m-1)*(a+b*ArcTan[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2+e^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/e*Int[x^(m-1)*(a+b*ArcCot[c*x])^n,x] -
  d/e*Int[x^(m-1)*(a+b*ArcCot[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2+e^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcTan[c*x])^n*Log[2*e*x/(d+e*x)]/d - 
  b*c*n/d*Int[(a+b*ArcTan[c*x])^(n-1)*Log[2*e*x/(d+e*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2+e^2] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcCot[c*x])^n*Log[2*e*x/(d+e*x)]/d +
  b*c*n/d*Int[(a+b*ArcCot[c*x])^(n-1)*Log[2*e*x/(d+e*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2+e^2] && PositiveIntegerQ[n]


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTan[c*x])^n,x] -
  e/d*Int[x^(m+1)*(a+b*ArcTan[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2+e^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCot[c*x])^n,x] -
  e/d*Int[x^(m+1)*(a+b*ArcCot[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2+e^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcTan[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || NonzeroQ[a] || IntegerQ[m])


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcCot[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || NonzeroQ[a] || IntegerQ[m])


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^p/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcTan[c*x])/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[p] && p>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^p/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcCot[c*x])/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[p] && p>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  -b*n*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-1)/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x])^n,x] + 
  b^2*d*n*(n-1)/(2*p*(2*p+1))*Int[(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n,p] && p>0 && n>1


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  b*n*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-1)/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x])^n,x] + 
  b^2*d*n*(n-1)/(2*p*(2*p+1))*Int[(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n,p] && p>0 && n>1


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcTan[c_.*x_])),x_Symbol] :=
  Log[RemoveContent[a+b*ArcTan[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCot[c_.*x_])),x_Symbol] :=
  -Log[RemoveContent[a+b*ArcCot[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && NonzeroQ[n+1]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && NonzeroQ[n+1]


Int[(a_.+b_.*ArcTan[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*I*(a+b*ArcTan[c*x])*ArcTan[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,-I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d]


Int[(a_.+b_.*ArcCot[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*I*(a+b*ArcCot[c*x])*ArcTan[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,-I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c*Sqrt[d])*Subst[Int[(a+b*x)^n*Sec[x],x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -x*Sqrt[1+1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n*Csc[x],x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTan[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCot[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^n/(2*d*(d+e*x^2)) + 
  (a+b*ArcTan[c*x])^(n+1)/(2*b*c*d^2*(n+1)) - 
  b*c*n/2*Int[x*(a+b*ArcTan[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcCot[c*x])^n/(2*d*(d+e*x^2)) - 
  (a+b*ArcCot[c*x])^(n+1)/(2*b*c*d^2*(n+1)) + 
  b*c*n/2*Int[x*(a+b*ArcCot[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcTan[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTan[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d]


Int[(a_.+b_.*ArcCot[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCot[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^(p+1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[p] && p<-1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(p+1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[p] && p<-1 && p!=-3/2


Int[(a_.+b_.*ArcTan[c_.*x_])^n_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  b*n*(a+b*ArcTan[c*x])^(n-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTan[c*x])^n/(d*Sqrt[d+e*x^2]) -
  b^2*n*(n-1)*Int[(a+b*ArcTan[c*x])^(n-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>1


Int[(a_.+b_.*ArcCot[c_.*x_])^n_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b*n*(a+b*ArcCot[c*x])^(n-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCot[c*x])^n/(d*Sqrt[d+e*x^2]) -
  b^2*n*(n-1)*Int[(a+b*ArcCot[c*x])^(n-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  b*n*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n-1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n,x] -
  b^2*n*(n-1)/(4*(p+1)^2)*Int[(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n,p] && p<-1 && n>1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  -b*n*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n-1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n,x] -
  b^2*n*(n-1)/(4*(p+1)^2)*Int[(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n,p] && p<-1 && n>1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  2*c*(p+1)/(b*(n+1))*Int[x*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n,p] && p<-1 && n<-1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  -(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  2*c*(p+1)/(b*(n+1))*Int[x*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n,p] && p<-1 && n<-1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d^p/c*Subst[Int[(a+b*x)^n/Cos[x]^(2*(p+1)),x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && NegativeIntegerQ[2*(p+1)] && (IntegerQ[p] || PositiveQ[d])


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(1+c^2*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && NegativeIntegerQ[2*(p+1)] && Not[IntegerQ[p] || PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c*Subst[Int[(a+b*x)^n/Sin[x]^(2*(p+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && NegativeIntegerQ[2*(p+1)] && IntegerQ[p]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -d^(p+1/2)*x*Sqrt[(1+c^2*x^2)/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n/Sin[x]^(2*(p+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && NegativeIntegerQ[2*(p+1)] && Not[IntegerQ[p]]


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


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcTan[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcCot[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTan[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCot[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m<-1


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^(n+1)/(b*e*(n+1)) - 
  1/(c*d)*Int[(a+b*ArcTan[c*x])^n/(I-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^(n+1)/(b*e*(n+1)) - 
  1/(c*d)*Int[(a+b*ArcCot[c*x])^n/(I-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n]


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  x*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  1/(b*c*d*(n+1))*Int[(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && Not[PositiveIntegerQ[n]] && NonzeroQ[n+1]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  -x*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  1/(b*c*d*(n+1))*Int[(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && Not[PositiveIntegerQ[n]] && NonzeroQ[n+1]


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcTan[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcCot[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n] && n>0 && m>1


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^(n+1)/(b*d*(n+1)) +
  I/d*Int[(a+b*ArcTan[c*x])^n/(x*(I+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^(n+1)/(b*d*(n+1)) +
  I/d*Int[(a+b*ArcCot[c*x])^n/(x*(I+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTan[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCot[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  x^m*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*d*(n+1))*Int[x^(m-1)*(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n<-1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  -x^m*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  m/(b*c*d*(n+1))*Int[x^(m-1)*(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n<-1


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTan[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[m==1 && NonzeroQ[a]]


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCot[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[m==1 && NonzeroQ[a]]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n/(2*e*(p+1)) - 
  b*n/(2*c*(p+1))*Int[(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && NonzeroQ[p+1]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n/(2*e*(p+1)) +
  b*n/(2*c*(p+1))*Int[(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && NonzeroQ[p+1]


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^n_/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)*(d+e*x^2)) -
  (1-c^2*x^2)*(a+b*ArcTan[c*x])^(n+2)/(b^2*e*(n+1)*(n+2)*(d+e*x^2)) -
  4/(b^2*(n+1)*(n+2))*Int[x*(a+b*ArcTan[c*x])^(n+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n<-1 && n!=-2


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^n_/(d_+e_.*x_^2)^2,x_Symbol] :=
  -x*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)*(d+e*x^2)) -
  (1-c^2*x^2)*(a+b*ArcCot[c*x])^(n+2)/(b^2*e*(n+1)*(n+2)*(d+e*x^2)) -
  4/(b^2*(n+1)*(n+2))*Int[x*(a+b*ArcCot[c*x])^(n+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n<-1 && n!=-2


Int[x_^2*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(p+1)/(4*c^3*d*(p+1)^2) + 
  x*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])/(2*c^2*d*(p+1)) - 
  1/(2*c^2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[p] && p<-1 && p!=-5/2


Int[x_^2*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^(p+1)/(4*c^3*d*(p+1)^2) + 
  x*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])/(2*c^2*d*(p+1)) - 
  1/(2*c^2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[p] && p<-1 && p!=-5/2


Int[x_^2*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  (a+b*ArcTan[c*x])^(n+1)/(2*b*c^3*d^2*(n+1)) - 
  x*(a+b*ArcTan[c*x])^n/(2*c^2*d*(d+e*x^2)) + 
  b*n/(2*c)*Int[x*(a+b*ArcTan[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0


Int[x_^2*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  -(a+b*ArcCot[c*x])^(n+1)/(2*b*c^3*d^2*(n+1)) - 
  x*(a+b*ArcCot[c*x])^n/(2*c^2*d*(d+e*x^2)) - 
  b*n/(2*c)*Int[x*(a+b*ArcCot[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  b*x^m*(d+e*x^2)^(p+1)/(c*d*m^2) - 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])/(c^2*d*m) + 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && ZeroQ[m+2*p+2] && RationalQ[p] && p<-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  -b*x^m*(d+e*x^2)^(p+1)/(c*d*m^2) - 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])/(c^2*d*m) + 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && ZeroQ[m+2*p+2] && RationalQ[p] && p<-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  b*n*x^m*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n-1)/(c*d*m^2) - 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n/(c^2*d*m) - 
  b^2*n*(n-1)/m^2*Int[x^m*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-2),x] + 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && ZeroQ[m+2*p+2] && RationalQ[n,p] && p<-1 && n>1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  -b*n*x^m*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n-1)/(c*d*m^2) - 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n/(c^2*d*m) - 
  b^2*n*(n-1)/m^2*Int[x^m*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-2),x] + 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && ZeroQ[m+2*p+2] && RationalQ[n,p] && p<-1 && n>1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[e-c^2*d] && ZeroQ[m+2*p+2] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  -x^m*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[e-c^2*d] && ZeroQ[m+2*p+2] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n/(d*(m+1)) - 
  b*c*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[e-c^2*d] && ZeroQ[m+2*p+3] && RationalQ[n] && n>0 && NonzeroQ[m+1]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n/(d*(m+1)) + 
  b*c*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[e-c^2*d] && ZeroQ[m+2*p+3] && RationalQ[n] && n>0 && NonzeroQ[m+1]


Int[x_^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])/(m+2) - 
  b*c*d/(m+2)*Int[x^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[x^m*(a+b*ArcTan[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && NonzeroQ[m+2]


Int[x_^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])/(m+2) + 
  b*c*d/(m+2)*Int[x^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[x^m*(a+b*ArcCot[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && NonzeroQ[m+2]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x])^n,x] + 
  c^2*d*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && RationalQ[p] && p>0 && PositiveIntegerQ[n] && (RationalQ[m] || OneQ[n] && IntegerQ[p])


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  d*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x])^n,x] + 
  c^2*d*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && RationalQ[p] && p>0 && PositiveIntegerQ[n] && (RationalQ[m] || OneQ[n] && IntegerQ[p])


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^n/(c^2*d*m) - 
  b*n/(c*m)*Int[x^(m-1)*(a+b*ArcTan[c*x])^(n-1)/Sqrt[d+e*x^2],x] - 
  (m-1)/(c^2*m)*Int[x^(m-2)*(a+b*ArcTan[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^n/(c^2*d*m) + 
  b*n/(c*m)*Int[x^(m-1)*(a+b*ArcCot[c*x])^(n-1)/Sqrt[d+e*x^2],x] - 
  (m-1)/(c^2*m)*Int[x^(m-2)*(a+b*ArcCot[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n] && n>0 && m>1


Int[(a_.+b_.*ArcTan[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcTan[c*x])*ArcTanh[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] + 
  I*b/Sqrt[d]*PolyLog[2,-Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] - 
  I*b/Sqrt[d]*PolyLog[2,Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d]


Int[(a_.+b_.*ArcCot[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcCot[c*x])*ArcTanh[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] - 
  I*b/Sqrt[d]*PolyLog[2,-Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] + 
  I*b/Sqrt[d]*PolyLog[2,Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  1/Sqrt[d]*Subst[Int[(a+b*x)^n*Csc[x],x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -c*x*Sqrt[1+1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n*Sec[x],x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTan[c*x])^n/(x*Sqrt[1+c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCot[c*x])^n/(x*Sqrt[1+c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^n/(d*x) + 
  b*c*n*Int[(a+b*ArcTan[c*x])^(n-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^n/(d*x) - 
  b*c*n*Int[(a+b*ArcCot[c*x])^(n-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^n/(d*(m+1)) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcTan[c*x])^(n-1)/Sqrt[d+e*x^2],x] - 
  c^2*(m+2)/(m+1)*Int[x^(m+2)*(a+b*ArcTan[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^n/(d*(m+1)) + 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCot[c*x])^(n-1)/Sqrt[d+e*x^2],x] - 
  c^2*(m+2)/(m+1)*Int[x^(m+2)*(a+b*ArcCot[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n+1),x] - 
  c*(m+2*p+2)/(b*(n+1))*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n,p] && p<-1 && n<-1 && NonzeroQ[m+2*p+2]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -x^m*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n+1),x] + 
  c*(m+2*p+2)/(b*(n+1))*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[m,n,p] && p<-1 && n<-1 && NonzeroQ[m+2*p+2]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]^m/Cos[x]^(m+2*(p+1)),x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && (IntegerQ[p] || PositiveQ[d])


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[x^m*(1+c^2*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && Not[IntegerQ[p] || PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]^m/Sin[x]^(m+2*(p+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -d^(p+1/2)*x*Sqrt[(1+c^2*x^2)/(c^2*x^2)]/(c^m*Sqrt[d+e*x^2])*Subst[Int[(a+b*x)^n*Cos[x]^m/Sin[x]^(m+2*(p+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && Not[IntegerQ[p]]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])/(2*e*(p+1)) - 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])/(2*e*(p+1)) + 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTan[c*x])^n,x^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || p<-1 && IntegerQ[m] && m!=1)


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCot[c*x])^n,x^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || p<-1 && IntegerQ[m] && m!=1)


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  a*Int[x^m*(d+e*x^2)^p,x] + b*Int[x^m*(d+e*x^2)^p*ArcTan[c*x],x] /;
FreeQ[{a,b,c,d,e,m,p},x]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  a*Int[x^m*(d+e*x^2)^p,x] + b*Int[x^m*(d+e*x^2)^p*ArcCot[c*x],x] /;
FreeQ[{a,b,c,d,e,m,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[ArcTanh[u_]*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+c*x))^2]


Int[ArcCoth[u_]*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+c*x))^2]


Int[ArcTanh[u_]*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-c*x))^2]


Int[ArcCoth[u_]*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-c*x))^2]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcTan[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) -
  b*n*I/2*Int[(a+b*ArcTan[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I+c*x))^2]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) +
  b*n*I/2*Int[(a+b*ArcCot[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I+c*x))^2]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) +
  b*n*I/2*Int[(a+b*ArcTan[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I-c*x))^2]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcCot[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) -
  b*n*I/2*Int[(a+b*ArcCot[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I-c*x))^2]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^n*PolyLog[p+1,u]/(2*c*d) +
  b*n*I/2*Int[(a+b*ArcTan[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+c*x))^2]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcCot[c*x])^n*PolyLog[p+1,u]/(2*c*d) -
  b*n*I/2*Int[(a+b*ArcCot[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+c*x))^2]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcTan[c*x])^n*PolyLog[p+1,u]/(2*c*d) -
  b*n*I/2*Int[(a+b*ArcTan[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-c*x))^2]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^n*PolyLog[p+1,u]/(2*c*d) +
  b*n*I/2*Int[(a+b*ArcCot[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[e-c^2*d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-c*x))^2]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCot[c_.*x_])*(a_.+b_.*ArcTan[c_.*x_])),x_Symbol] :=
  (-Log[a+b*ArcCot[c*x]]+Log[a+b*ArcTan[c*x]])/(b*c*d*(2*a+b*ArcCot[c*x]+b*ArcTan[c*x])) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d]


Int[(a_.+b_.*ArcCot[c_.*x_])^m_.*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCot[c*x])^(m+1)*(a+b*ArcTan[c*x])^n/(b*c*d*(m+1)) +
  n/(m+1)*Int[(a+b*ArcCot[c*x])^(m+1)*(a+b*ArcTan[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegersQ[m,n] && 0<n<=m


Int[(a_.+b_.*ArcTan[c_.*x_])^m_.*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTan[c*x])^(m+1)*(a+b*ArcCot[c*x])^n/(b*c*d*(m+1)) +
  n/(m+1)*Int[(a+b*ArcTan[c*x])^(m+1)*(a+b*ArcCot[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegersQ[m,n] && 0<n<m


Int[ArcTan[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I*a*x]/(c+d*x^n),x] -
  I/2*Int[Log[1+I*a*x]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[d-a^2*c]]


Int[ArcCot[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I/(a*x)]/(c+d*x^n),x] -
  I/2*Int[Log[1+I/(a*x)]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[d-a^2*c]]


Int[(a_.+b_.*ArcTan[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  x*(a+b*ArcTan[c*x])*(d+e*Log[f+g*x^2]) - 
  2*e*g*Int[x^2*(a+b*ArcTan[c*x])/(f+g*x^2),x] - 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[(a_.+b_.*ArcCot[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  x*(a+b*ArcCot[c*x])*(d+e*Log[f+g*x^2]) - 
  2*e*g*Int[x^2*(a+b*ArcCot[c*x])/(f+g*x^2),x] + 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  x^(m+1)*(a+b*ArcTan[c*x])*(d+e*Log[f+g*x^2])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcTan[c*x])/(f+g*x^2),x] - 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[m/2]


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  x^(m+1)*(a+b*ArcCot[c*x])*(d+e*Log[f+g*x^2])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcCot[c*x])/(f+g*x^2),x] + 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[m/2]


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*Log[f+g*x^2]),x]]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[(m+1)/2]


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*Log[f+g*x^2]),x]]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[(m+1)/2]


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(a+b*ArcTan[c*x]),x]]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && m!=-1


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(a+b*ArcCot[c*x]),x]]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && m!=-1


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^2*(d_.+e_.*Log[f_+g_.*x_^2]),x_Symbol] :=
  (f+g*x^2)*(a+b*ArcTan[c*x])^2*(d+e*Log[f+g*x^2])/(2*g) - 
  e*x^2*(a+b*ArcTan[c*x])^2/2 - 
  b/c*Int[(a+b*ArcTan[c*x])*(d+e*Log[f+g*x^2]),x] + 
  b*c*e*Int[x^2*(a+b*ArcTan[c*x])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[g-c^2*f]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^2*(d_.+e_.*Log[f_+g_.*x_^2]),x_Symbol] :=
  (f+g*x^2)*(a+b*ArcCot[c*x])^2*(d+e*Log[f+g*x^2])/(2*g) - 
  e*x^2*(a+b*ArcCot[c*x])^2/2 + 
  b/c*Int[(a+b*ArcCot[c*x])*(d+e*Log[f+g*x^2]),x] - 
  b*c*e*Int[x^2*(a+b*ArcCot[c*x])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[g-c^2*f]


Int[(a_.+b_.*ArcTan[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcTan[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCot[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCot[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcTan[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcTan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcCot[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcCot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[PositiveIntegerQ[n]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTan[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcTan[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && PositiveIntegerQ[n]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCot[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCot[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && PositiveIntegerQ[n]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcTan[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcTan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[PositiveIntegerQ[n]]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCot[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcCot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[PositiveIntegerQ[n]]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^p*(a+b*ArcTan[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && ZeroQ[B*(1+c^2)-2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^p*(a+b*ArcCot[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && ZeroQ[B*(1+c^2)-2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^p*(a+b*ArcTan[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && ZeroQ[B*(1+c^2)-2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^p*(a+b*ArcCot[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && ZeroQ[B*(1+c^2)-2*A*c*d] && ZeroQ[2*c*C-B*d]


(* ::Subsection::Closed:: *)
(*Inverse Sine Functions*)


Int[ArcSin[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Cot[x],x],x,ArcSin[a*x^p]] /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0


Int[ArcCos[a_.*x_^p_]^n_./x_,x_Symbol] :=
  -1/p*Subst[Int[x^n*Tan[x],x],x,ArcCos[a*x^p]] /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0


Int[u_.*ArcSin[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCsc[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCos[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSec[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*f_^(c_.*ArcSin[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[ReplaceAll[u,x->-a/b+Sin[x]/b]*f^(c*x^n)*Cos[x],x],x,ArcSin[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[u_.*f_^(c_.*ArcCos[a_.+b_.*x_]^n_.),x_Symbol] :=
  -1/b*Subst[Int[ReplaceAll[u,x->-a/b+Cos[x]/b]*f^(c*x^n)*Sin[x],x],x,ArcCos[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


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
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCos[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCos[u])/(d*(m+1)) +
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSin[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcSin[u]),w,x] -
  b*Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCos[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcCos[u]),w,x] +
  b*Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


(* ::Subsection::Closed:: *)
(*Inverse Tangent Functions*)


Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*x]/(c+d*x^n),x] -
  I/2*Int[Log[1+I*a+I*b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[(-I+a+b*x)/(a+b*x)]/(c+d*x^n),x] -
  I/2*Int[Log[(I+a+b*x)/(a+b*x)]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcTan[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcCot[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


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


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  1/c*Log[ArcTan[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && ZeroQ[b+c^2]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  -1/c*Log[ArcCot[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && ZeroQ[b+c^2]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  ArcTan[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && ZeroQ[b+c^2] && NonzeroQ[m+1]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  -ArcCot[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && ZeroQ[b+c^2] && NonzeroQ[m+1]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcTan[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b+c^2] && ZeroQ[b*d-a*e]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcCot[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b+c^2] && ZeroQ[b*d-a*e]


Int[E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[a,x] && RationalQ[I*n]


Int[E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  4*(I-a*x)*E^(n*ArcTan[a*x])/(a*(n+2*I)*(I+a*x))*Hypergeometric2F1[2,1-I*n/2,2-I*n/2,-E^(2*I*ArcTan[a*x])] /;
FreeQ[{a,n},x] && Not[RationalQ[I*n]]


Int[x_^m_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[x^m*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,m,n},x]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1+d*x/c)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2+d^2] && (IntegerQ[p] || PositiveQ[c])


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[u*(c+d*x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2+d^2] && Not[IntegerQ[p] || PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[c^2+a^2*d^2] && IntegerQ[p]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*c^p*Int[u*(1+d/(c*x))^p*(1-1/(I*a*x))^(I*n/2)/(1+1/(I*a*x))^(I*n/2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  Int[u*(c+d/x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  x^p*(c+d/x)^p/(1+c*x/d)^p*Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[p]]


Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcTan[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c]


Int[E^(n_*ArcTan[a_.*x_])/Sqrt[1+d_.*x_^2],x_Symbol] :=
  Int[1/(1-a*n*x),x] /;
FreeQ[{a,d,n},x] && ZeroQ[d-a^2] && ZeroQ[n^2+1]


Int[E^(n_*ArcTan[a_.*x_])/Sqrt[c_.+d_.*x_^2],x_Symbol] :=
  Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[E^(n*ArcTan[a*x])/Sqrt[1+a^2*x^2],x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+1] && NonzeroQ[c-1]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*a*p*x)*(c+d*x^2)^p*E^(n*ArcTan[a*x])/(2*a*p*(2*p+1)) /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+4*p^2] && NonzeroQ[p+1/2]


(* Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*a*p*x)*(c+d*x^2)^p*E^(n*ArcTan[a*x])/(2*a*p*(2*p+1)) + 
  c*(n^2+4*p^2)/(2*p*(2*p+1))*Int[(c+d*x^2)^(p-1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n^2+4*p^2] && RationalQ[p] && p>0 *)


Int[E^(n_*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  1/c^(3/2)*Int[1/((1+a*n*x)*(1-a*n*x)^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+1] && PositiveQ[c]


Int[E^(n_*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  Sqrt[1+a^2*x^2]/(c*Sqrt[c+d*x^2])*Int[E^(n*ArcTan[a*x])/(1+a^2*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+1] && Not[PositiveQ[c]]


Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n+a*x)*E^(n*ArcTan[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n^2+9] && NonzeroQ[n^2+1]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (n-2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*c*(n^2+4*(p+1)^2)) + 
  2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n^2+4*p^2] && RationalQ[p] && p<-1 && p!=-3/2 && NonzeroQ[n^2+4*(p+1)^2] && 
  IntegerQ[2*p]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[(1+a^2*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c]) && OddQ[I*n]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c]) && Not[OddQ[I*n]] && 
  (RationalQ[I*n,p] || PositiveIntegerQ[p-I*n/2] || PositiveIntegerQ[p+I*n/2])


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  1/c^(I*n/2)*Int[(c+d*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && EvenQ[I*n] && RationalQ[p]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && PositiveIntegerQ[p+1/2] && RationalQ[I*n]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && NegativeIntegerQ[p-1/2] && RationalQ[I*n]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(1+a^2*x^2)^p*Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[p+1/2]] && 
  (RationalQ[n,p] || PositiveIntegerQ[p-n/2] || PositiveIntegerQ[p+n/2])


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+a^2*c*x^2)^(p+1)*E^(n*ArcTan[a*x])/(2*a*c*n)*(1+E^(n/(p+1)*ArcTan[a*x]))^(2*(p+1))*
    Hypergeometric2F1[2*(p+1),2*(p+1),2*p+3,-E^(n/(p+1)*ArcTan[a*x])] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2+4*(p+1)^2] && Not[IntegerQ[2*p]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  4^(p+1)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*c*(n+2*I*(p+1)))*(1/(1-I*a*x))^(2*(p+1))*
    Hypergeometric2F1[p-I*n/2+1,2*(p+1),p-I*n/2+2,-E^(2*I*ArcTan[a*x])] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && NonzeroQ[n^2+4*(p+1)^2] && Not[NegativeIntegerQ[2*p+1]] && Not[IntegerQ[p-I*n/2]]


Int[x_*E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcTan[a*x])/(a^2*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[OddQ[I*n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a^2*c*(n^2+4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<=-1 && p!=-3/2 && NonzeroQ[n^2+4*(p+1)^2] && Not[OddQ[I*n]]


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a^3*c*n^2*(n^2+1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2-2*(p+1)] && NonzeroQ[n^2+1]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a^3*c*(n^2+4*(p+1)^2)) + 
  (n^2-2*(p+1))/(a^2*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<=-1 && NonzeroQ[n^2-2*(p+1)] && NonzeroQ[n^2+4*(p+1)^2] && Not[OddQ[I*n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p/a^(m+1)*Subst[Int[E^(n*x)*Tan[x]^(m+2*(p+1))/Sin[x]^(2*(p+1)),x],x,ArcTan[a*x]] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && IntegerQ[m] && RationalQ[p] && 3<=m<=-2(p+1) && IntegerQ[2*p] && (IntegerQ[p] || PositiveQ[c])


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1+a^2*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c]) && OddQ[I*n] && 
  (Not[RationalQ[p]] || Not[RationalQ[m]] || ZeroQ[I*n-1] && NonzeroQ[p+1])


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  1/c^(I*n/2)*Int[x^m*(c+d*x^2)^(p+I*n/2)/(1+a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && IntegerQ[I*n/2] && 
  (ZeroQ[m-1] || Not[IntegerQ[p+1/2]])


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c])


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/(Sqrt[1-I*a*x]*Sqrt[1+I*a*x])*Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && IntegerQ[I*n/2] && PositiveIntegerQ[p+1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1-I*a*x]*Sqrt[1+I*a*x]/Sqrt[c+d*x^2]*Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && IntegerQ[I*n/2] && NegativeIntegerQ[p-1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && Not[IntegerQ[I*n/2]] && PositiveIntegerQ[p+1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]] && Not[IntegerQ[I*n/2]] && NegativeIntegerQ[p-1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(1+a^2*x^2)^p*Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p+1/2]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[c-a^2*d] && IntegerQ[p]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-I/(a*x))^p*(1+I/(a*x))^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/((1-I*a*x)^p*(1+I*a*x)^p)*Int[u/x^(2*p)*(1-I*a*x)^p*(1+I*a*x)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/(1+a^2*x^2)^p*Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[p]] && Not[IntegerQ[I*n/2]]


Int[u_.*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  (-1)^(I*n/2)*Int[u*E^(-n*ArcTan[a*x]),x] /;
FreeQ[a,x] && IntegerQ[I*n/2]


Int[E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[I*n/2]]


Int[x_^m_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[I*n/2]] && IntegerQ[m]


Int[x_^m_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[m]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c^2+d^2] && Not[IntegerQ[I*n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(x^p*(1+c/(d*x))^p)*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2+d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]


Int[(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c])


Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegerQ[m]


Int[(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[x_^m_*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[u*(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  -E^(n*ArcCot[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c]


Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(n-a*x)*E^(n*ArcCot[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[OddQ[I*n]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -(n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a*c*(n^2+4*(p+1)^2)) + 
  2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<-1 && p!=-3/2 && NonzeroQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_*E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1+a*n*x)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[OddQ[I*n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (2*(p+1)-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+4*(p+1)^2)) + 
  n*(2*p+3)/(a*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<=-1 && p!=-3/2 && NonzeroQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*n^2*(n^2+1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && ZeroQ[n^2-2*(p+1)] && NonzeroQ[n^2+1]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*(n^2+4*(p+1)^2)) + 
  (n^2-2*(p+1))/(a^2*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && RationalQ[p] && p<=-1 && NonzeroQ[n^2-2*(p+1)] && NonzeroQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p/a^(m+1)*Subst[Int[E^(n*x)*Cot[x]^(m+2*(p+1))/Cos[x]^(2*(p+1)),x],x,ArcCot[a*x]] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && IntegerQ[m] && 3<=m<=-2(p+1) && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[I*n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(x^(2*p)*(1+1/(a^2*x^2))^p)*Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[d-a^2*c] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  c^p/(I*a)^(2*p)*Int[u/x^(2*p)*(-1+I*a*x)^(p-I*n/2)*(1+I*a*x)^(p+I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegersQ[2*p,p+I*n/2]


Int[(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^2,x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]]


Int[x_^m_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]] && 
  IntegerQ[m]


Int[x_^m_*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]] && 
  Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x^2)^p/(1+1/(a^2*x^2))^p*Int[u*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,n},x]


Int[x_^m_*E^(n_*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(I^m*n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/(I*n))*(1-I*a*c-(1+I*a*c)*x^(2/(I*n)))^m/(1+x^(2/(I*n)))^(m+2),x],x,
      (1-I*c*(a+b*x))^(I*n/2)/(1+I*c*(a+b*x))^(I*n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[I*n] && -1<I*n<1


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(d+e*x)^m*(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
  (c/(1+a^2))^p*Int[u*(1-I*a-I*b*x)^(p+I*n/2)*(1+I*a+I*b*x)^(p-I*n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c-e(1+a^2)] && (IntegerQ[p] || PositiveQ[c/(1+a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p*Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c-e(1+a^2)] && Not[IntegerQ[p] || PositiveQ[c/(1+a^2)]]


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
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[I*n] && -1<I*n<1


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (I*c*(a+b*x))^(I*n/2)*(1+1/(I*c*(a+b*x)))^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2)*
    Int[(d+e*x)^m*(1+I*a*c+I*b*c*x)^(I*n/2)/(-1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[I*n/2]]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
  (c/(1+a^2))^p*((I*a+I*b*x)/(1+I*a+I*b*x))^(I*n/2)*((1+I*a+I*b*x)/(I*a+I*b*x))^(I*n/2)*
    ((1-I*a-I*b*x)^(I*n/2)/(-1+I*a+I*b*x)^(I*n/2))*
    Int[u*(1-I*a-I*b*x)^(p-I*n/2)*(1+I*a+I*b*x)^(p+I*n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c-e(1+a^2)] && 
  (IntegerQ[p] || PositiveQ[c/(1+a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p*Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c-e(1+a^2)] && 
  Not[IntegerQ[p] || PositiveQ[c/(1+a^2)]]


Int[u_.*E^(n_.*ArcTan[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcCot[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*E^(n_.*ArcCot[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcTan[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*ArcTan[v_+s_.*Sqrt[w_]],x_Symbol] :=
  Pi*s/4*Int[u,x] + 1/2*Int[u*ArcTan[v],x] /;
ZeroQ[s^2-1] && ZeroQ[w-(v^2+1)]


Int[u_.*ArcCot[v_+s_.*Sqrt[w_]],x_Symbol] :=
  Pi*s/4*Int[u,x] - 1/2*Int[u*ArcTan[v],x] /;
ZeroQ[s^2-1] && ZeroQ[w-(v^2+1)]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcTan[a+b*x]]/(1+(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Tan[x]/b,x],x],x,ArcTan[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTan && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTan && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcCot[a+b*x]]/(1+(a+b*x)^2),x]",
		   "-Subst[Int[f[-a/b+Cot[x]/b,x],x],x,ArcCot[a+b*x]]/b",Hold[
  -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCot && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCot && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


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
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCot[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCot[u])/(d*(m+1)) +
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1+u^2),x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[v_*(a_.+b_.*ArcTan[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcTan[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcTan[u]),x]]


Int[v_*(a_.+b_.*ArcCot[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcCot[u]),w,x] + b*Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcCot[u]),x]]


Int[ArcTan[v_]*Log[w_]/(a_.+b_.*x_),x_Symbol] :=
  I/2*Int[Log[1-I*v]*Log[w]/(a+b*x),x] - I/2*Int[Log[1+I*v]*Log[w]/(a+b*x),x] /;
FreeQ[{a,b},x] && LinearQ[v,x] && LinearQ[w,x] && ZeroQ[Simplify[D[v/(a+b*x),x]]] && ZeroQ[Simplify[D[w/(a+b*x),x]]]


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
  Module[{z=Block[{ShowSteps=False,StepCounter=Null}, Int[u,x]]},  
  Dist[ArcTan[v]*Log[w],z,x] - 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[z*ArcTan[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*ArcCot[v_]*Log[w_],x_Symbol] :=
  Module[{z=Block[{ShowSteps=False,StepCounter=Null}, Int[u,x]]},  
  Dist[ArcCot[v]*Log[w],z,x] + 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[z*ArcCot[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


(* ::Subsection::Closed:: *)
(*Inverse Secant Functions*)


Int[ArcSec[c_.*x_],x_Symbol] :=
  x*ArcSec[c*x] - 1/c*Int[1/(x*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[c,x]


Int[ArcCsc[c_.*x_],x_Symbol] :=
  x*ArcCsc[c*x] + 1/c*Int[1/(x*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[c,x]


Int[(a_.+b_.*ArcSec[c_.*x_])^n_,x_Symbol] :=
  1/c*Subst[Int[(a+b*x)^n*Sec[x]*Tan[x],x],x,ArcSec[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcCsc[c_.*x_])^n_,x_Symbol] :=
  -1/c*Subst[Int[(a+b*x)^n*Csc[x]*Cot[x],x],x,ArcCsc[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcSec[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcCos[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcCsc[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcSin[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[x_^m_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  x^(m+1)*(a+b*ArcSec[c*x])/(m+1) - 
  b/(c*(m+1))*Int[x^(m-1)/Sqrt[1-1/(c^2*x^2)],x] /;
FreeQ[{a,b,c,m},x] && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  x^(m+1)*(a+b*ArcCsc[c*x])/(m+1) +
  b/(c*(m+1))*Int[x^(m-1)/Sqrt[1-1/(c^2*x^2)],x] /;
FreeQ[{a,b,c,m},x] && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcSec[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Sec[x]^(m+1)*Tan[x],x],x,ArcSec[c*x]] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcCsc[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Csc[x]^(m+1)*Cot[x],x],x,ArcCsc[c*x]] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*ArcSec[c*x])^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[x_^m_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*ArcCsc[c*x])^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[(a+b*ArcSec[c*x]),u,x] - b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[(a+b*ArcCsc[c*x]),u,x] + b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcSec[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCsc[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSec[c*x])/(2*e*(p+1)) - 
  b*c*x/(2*e*(p+1)*Sqrt[c^2*x^2])*Int[(d+e*x^2)^(p+1)/(x*Sqrt[c^2*x^2-1]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCsc[c*x])/(2*e*(p+1)) + 
  b*c*x/(2*e*(p+1)*Sqrt[c^2*x^2])*Int[(d+e*x^2)^(p+1)/(x*Sqrt[c^2*x^2-1]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[(a+b*ArcSec[c*x]),u,x] - b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[(a+b*ArcCsc[c*x]),u,x] + b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegersQ[m,p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegersQ[m,p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcSec[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcCsc[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[ArcSec[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcSec[a+b*x]/b - 
  Int[1/((a+b*x)*Sqrt[1-1/(a+b*x)^2]),x] /;
FreeQ[{a,b},x]


Int[ArcCsc[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcCsc[a+b*x]/b + 
  Int[1/((a+b*x)*Sqrt[1-1/(a+b*x)^2]),x] /;
FreeQ[{a,b},x]


Int[ArcSec[a_+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[x^n*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcCsc[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[x^n*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcSec[a_+b_.*x_]/x_,x_Symbol] :=
  ArcSec[a+b*x]*Log[1-(1-Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] + 
  ArcSec[a+b*x]*Log[1-(1+Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] - 
  ArcSec[a+b*x]*Log[1+E^(2*I*ArcSec[a+b*x])] - 
  I*PolyLog[2,(1-Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] - 
  I*PolyLog[2,(1+Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] + 
  1/2*I*PolyLog[2,-E^(2*I*ArcSec[a+b*x])] /;
FreeQ[{a,b},x]


Int[ArcCsc[a_+b_.*x_]/x_,x_Symbol] :=
  I*ArcCsc[a+b*x]^2 + 
  ArcCsc[a+b*x]*Log[1-I*(1-Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  ArcCsc[a+b*x]*Log[1-I*(1+Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] - 
  ArcCsc[a+b*x]*Log[1-E^(2*I*ArcCsc[a+b*x])] + 
  I*PolyLog[2,I*(1-Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  I*PolyLog[2,I*(1+Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  1/2*I*PolyLog[2,E^(2*I*ArcCsc[a+b*x])] /;
FreeQ[{a,b},x]


Int[x_^m_.*ArcSec[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcSec[a+b*x]/(b^(m+1)*(m+1)) - 
  1/(b^(m+1)*(m+1))*Subst[Int[(((-a)*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1-x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NonzeroQ[m+1]


Int[x_^m_.*ArcCsc[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcCsc[a+b*x]/(b^(m+1)*(m+1)) + 
  1/(b^(m+1)*(m+1))*Subst[Int[(((-a)*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1-x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NonzeroQ[m+1]


Int[x_^m_.*ArcSec[a_+b_.*x_]^n_,x_Symbol] :=
  1/b^(m+1)*Subst[Int[x^n*(-a+Sec[x])^m*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,n},x] && PositiveIntegerQ[m]


Int[x_^m_.*ArcCsc[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b^(m+1)*Subst[Int[x^n*(-a+Csc[x])^m*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,n},x] && PositiveIntegerQ[m]


Int[u_.*ArcSec[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCos[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCsc[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSin[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*f_^(c_.*ArcSec[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[ReplaceAll[u,x->-a/b+Sec[x]/b]*f^(c*x^n)*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[u_.*f_^(c_.*ArcCsc[a_.+b_.*x_]^n_.),x_Symbol] :=
  -1/b*Subst[Int[ReplaceAll[u,x->-a/b+Csc[x]/b]*f^(c*x^n)*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


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
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCsc[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCsc[u])/(d*(m+1)) +
  b*u/(d*(m+1)*Sqrt[u^2])*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSec[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcSec[u]),w,x] - b*u/Sqrt[u^2]*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCsc[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcCsc[u]),w,x] + b*u/Sqrt[u^2]*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]
