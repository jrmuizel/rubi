(* ::Package:: *)

(* ::Section:: *)
(*Inverse Hyperbolic Function Rules*)


(* ::Subsection::Closed:: *)
(*u (a+b arcsinh(c x))^n*)


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcSinh[c*x])^n - 
  b*c*n*Int[x*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  c/(b*(n+1))*Int[x*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  1/(b*c)*Subst[Int[x^n*Cosh[a/b-x/b],x],x,a+b*ArcSinh[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcSinh[c*x])^n/(e*(m+1)) - 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && RationalQ[n] && n>0 && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1),Sinh[x]^(m-1)*(m+(m+1)*Sinh[x]^2),x],x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -2<=n<-1 && PositiveIntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] - 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-2 && PositiveIntegerQ[m]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[n] && n<-1 && PositiveIntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Cosh[x]*(c*d+e*Sinh[x])^m,x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[m] && (m>0 || PositiveIntegerQ[n])


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (PositiveIntegerQ[p] || NonzeroQ[a])


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[(d*f+e*g*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && IntegerQ[p]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[d*f+e*g*x^2]*Int[(d*f+e*g*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && PositiveIntegerQ[p+1/2]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[(d*f+e*g*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e*f+d*g] && NegativeIntegerQ[p-1/2]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x)^p*(f+g*x)^p,x]]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[p]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x)^p*(f+g*x)^p,x]]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[Dist[1/Sqrt[1+c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[p+1/2]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(f+g*x)^p*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[p]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(f+g*x)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(b*c*Sqrt[d])*Subst[Int[x^n,x],x,a+b*ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveQ[d]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(2*p+1) - 
  b*c*n*Sqrt[d]/(2*p+1)*Int[x*(d+e*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p>0


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/(c*d)*Subst[Int[(a+b*x)^n*Sech[x],x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcSinh[c*x])^n/(d*Sqrt[d+e*x^2]) - 
  b*c*n/Sqrt[d]*Int[x*(a+b*ArcSinh[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d] && RationalQ[n] && n>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*d*(p+1)) + 
  b*c*n/(2*Sqrt[d]*(p+1))*Int[x*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p<-1 && p!=-2/3


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  (d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  e*(2*p+1)/(b*c*Sqrt[d]*(n+1))*Int[x*(d+e*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n<-1 && p!=-1/2


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^p/c*Subst[Int[(a+b*x)^n*Cosh[x]^(2*p+1),x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[2*p] && PositiveQ[d]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^p*Int[(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && IntegerQ[p] && Not[PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]*Int[(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[p+1/2] && Not[PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && NegativeIntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && PositiveIntegerQ[p]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(Sqrt[d]-Sqrt[-e]*x)^p*(Sqrt[d]+Sqrt[-e]*x)^p*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NegativeIntegerQ[p] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[d*f+e*g*x^2]*Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && PositiveIntegerQ[p+1/2]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[x^m*(d*f+e*g*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f+d*g] && NegativeIntegerQ[p-1/2]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])/(2*e*(p+1)) - 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcSinh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*e*(p+1)) - 
  b*n/(2*c*Sqrt[d]*(p+1))*Int[(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(m+1) - 
  b*c*Sqrt[d]*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] - 
  2*e*p/(m+1)*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p>0 && m<-1


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(m+2*p+1) - 
  b*c*n*Sqrt[d]/(m+2*p+1)*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] + 
  2*d*p/(m+2*p+1)*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p>0 && m+2*p+1!=0


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(d*(m+1)) - 
  b*c*n/(Sqrt[d]*(m+1))*Int[x^(m+1)*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<0 && m!=-1 && m+2*p+3==0


Int[x_^m_*(a_.+b_.*ArcSinh[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*(a+b*ArcSinh[c*x])*Hypergeometric2F1[1/2,(m+1)/2,(m+3)/2,-c^2*x^2]/(Sqrt[d]*(m+1)) - 
  b*c*x^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},-c^2*x^2]/(Sqrt[d]*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d] && Not[IntegerQ[m]]


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/(c^(m+1)*d)*Subst[Int[(a+b*x)^n*Sinh[x]^m*Sech[x],x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d] && PositiveIntegerQ[n] && IntegerQ[m] && m^2==1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(e*(m+2*p+1)) - 
  b*c*Sqrt[d]*n/(e*(m+2*p+1))*Int[x^(m-1)*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] - 
  (m-1)/(c^2*(m+2*p+1))*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && -1<=p<0 && m>1 && NonzeroQ[m+2*p+1]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*e*(p+1)) - 
  b*n/(2*c*Sqrt[d]*(p+1))*Int[x^(m-1)*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] - 
  (m-1)/(2*e*(p+1))*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<-1 && m>1


Int[ArcSinh[c_.*x_]/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  2*ArcSinh[c*x]*ArcTanh[c*x-Sqrt[1+c^2*x^2]]/Sqrt[d] + 
  PolyLog[2,c*x-Sqrt[1+c^2*x^2]]/Sqrt[d] - 
  PolyLog[2,-c*x+Sqrt[1+c^2*x^2]]/Sqrt[d] /;
FreeQ[{c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d]


Int[(a_+b_.*ArcSinh[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  a*Int[1/(x*Sqrt[d+e*x^2]),x] + 
  b*Int[ArcSinh[c*x]/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && PositiveQ[d]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_./x_,x_Symbol] :=
  c^2*Int[x*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] + 
  1/d*Int[(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/x,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[n] && n>0 && p<-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(d*(m+1)) - 
  b*c*n/(Sqrt[d]*(m+1))*Int[x^(m+1)*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] - 
  c^2*(m+2*p+3)/(m+1)*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n>0 && p<0 && m<-1 && m+2*p+3!=0


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^m*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[e-c^2*d] && PositiveQ[d] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  d*m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n<-1 && m+2*p+1==0


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  d*m/(b*c*Sqrt[d]*(n+1))*Int[x^(m-1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] - 
  e*(m+2*p+1)/(b*c*Sqrt[d]*(n+1))*Int[x^(m+1)*(d+e*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[e-c^2*d] && IntegerQ[2*p] && PositiveQ[d] && RationalQ[m,n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] - 
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && NegativeIntegerQ[p+1/2] && PositiveQ[d] && NegativeIntegerQ[(m-1)/2]


Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*Sinh[x]^m,x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveQ[d] && IntegerQ[m] && (m>0 || PositiveIntegerQ[n])


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Sinh[x]^m*Cosh[x]^(2*p+1),x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[2*p] && PositiveQ[d] && PositiveIntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n/Sqrt[d+e*x^2],x^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[p+1/2] && PositiveQ[d] && Not[PositiveIntegerQ[(m+1)/2]]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^p*Int[x^m*(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[e-c^2*d] && IntegerQ[p] && Not[PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]*Int[x^m*(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[e-c^2*d] && PositiveIntegerQ[p+1/2] && Not[PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[x^m*(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[e-c^2*d] && NegativeIntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(h_.+i_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_./(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  Sqrt[d*f+e*g*x^2]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[(h+i*x)^m*(a+b*ArcSinh[c*x])^n/Sqrt[d*f+e*g*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n},x] && ZeroQ[e*f+d*g]


Int[(i_*x_)^m_*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (i*x)^m/x^m*Int[x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,i,m,n,p},x]


Int[(h_.+i_.*x_)^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(h+i*x)^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n,p},x]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f+g*x)^m*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && ZeroQ[e-c^2*d] && PositiveQ[d] && RationalQ[n] && n<-1


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*(c*f+g*Sinh[x])^m,x],x,ArcSinh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c^2*d] && PositiveQ[d] && IntegerQ[m]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(f+g*x)^m*(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e-c^2*d] && Not[PositiveQ[d]]


Int[(g_*x_)^m_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  (g*x)^m/x^m*Int[x^m*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,g,m,n,p},x]


Int[(f_.+g_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(f+g*x)^m*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


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
FreeQ[{a,b,c,d,A,B,C,n,p},x] && ZeroQ[B*(1+c^2)-2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^p*(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && ZeroQ[B*(1+c^2)-2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


(* ::Subsection::Closed:: *)
(*u (a+b arccosh(c x))^n*)


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcCosh[c*x])^n - 
  b*c*n*Int[x*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  Sqrt[-1+c*x]*Sqrt[1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) - 
  c/(b*(n+1))*Int[x*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  -1/(b*c)*Subst[Int[x^n*Sinh[a/b-x/b],x],x,a+b*ArcCosh[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCosh[c*x])/(e*(m+1)) - 
  b*c*Sqrt[1-c^2*x^2]/(e*(m+1)*Sqrt[-1+c*x]*Sqrt[1+c*x])*Int[(d+e*x)^(m+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m+1/2]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCosh[c*x])^n/(e*(m+1)) - 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,e,m},x] && RationalQ[n] && n>0 && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[-1+c*x]*Sqrt[1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1)*Cosh[x]^(m-1)*(m-(m+1)*Cosh[x]^2),x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c},x] && RationalQ[n] && -2<=n<-1 && PositiveIntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[-1+c*x]*Sqrt[1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] - 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-2 && PositiveIntegerQ[m]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[n] && n<-1 && PositiveIntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*(c*d+e*Cosh[x])^m*Sinh[x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[m] && (m>0 || PositiveIntegerQ[n])


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (PositiveIntegerQ[p] || NonzeroQ[a])


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  1/(b*c*Sqrt[d]*Sqrt[-f])*Subst[Int[x^n,x],x,a+b*ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n/(2*p+1) - 
  b*c*n*Sqrt[d]*Sqrt[-f]/(2*p+1)*Int[x*(d+e*x)^(p-1/2)*(f+g*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] + 
  2*d*f*p/(2*p+1)*Int[(d+e*x)^(p-1)*(f+g*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[n] && n>0 && p>0


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./((d_+e_.*x_)*(f_+g_.*x_)),x_Symbol] :=
  -1/(c*d*f)*Subst[Int[(a+b*x)^n*Csch[x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./((d_+e_.*x_)^(3/2)*(f_+g_.*x_)^(3/2)),x_Symbol] :=
  x*(a+b*ArcCosh[c*x])^n/(d*f*Sqrt[d+e*x]*Sqrt[f+g*x]) - 
  b*c*n/(Sqrt[d]*Sqrt[-f])*Int[x*(a+b*ArcCosh[c*x])^(n-1)/((d+e*x)*(f+g*x)),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f] && RationalQ[n] && n>0


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d*f*(p+1)) - 
  b*c*n/(2*Sqrt[d]*Sqrt[-f]*(p+1))*Int[x*(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] + 
  (2*p+3)/(2*d*f*(p+1))*Int[(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[n] && n>0 && p<-1 && p!=-2/3


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  (d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[d]*Sqrt[-f]*(n+1)) - 
  e*g*(2*p+1)/(b*c*Sqrt[d]*Sqrt[-f]*(n+1))*Int[x*(d+e*x)^(p-1/2)*(f+g*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[n] && n<-1 && p!=-1/2


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  d^p*(-f)^p/c*Subst[Int[(a+b*x)^n*Sinh[x]^(2*p+1),x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveIntegerQ[2*p] && PositiveQ[d] && NegativeQ[f]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  d^p*(-f)^p*Int[(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[p] && Not[PositiveQ[d] && NegativeQ[f]]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*(-f)^(p-1/2)*Sqrt[d+e*x]*Sqrt[f+g*x]/(Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveIntegerQ[p+1/2] && Not[PositiveQ[d] && NegativeQ[f]]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*(-f)^(p+1/2)*Sqrt[1+c*x]*Sqrt[-1+c*x]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && NegativeIntegerQ[p-1/2] && Not[PositiveQ[d] && NegativeQ[f]]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x)^p*(f+g*x)^p,x]]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[p]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x)^p*(f+g*x)^p,x]]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[Dist[1/(Sqrt[-1+c*x]*Sqrt[1+c*x]),u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[p+1/2]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[p]


Int[(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Sqrt[1-c^2*x^2]/(Sqrt[-1+c*x]*Sqrt[1+c*x])*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[(d-c*d*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d+e*x^2]/(Sqrt[d-c*d*x]*Sqrt[1+c*x])*Int[(d-c*d*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[p+1/2]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d-c*d*x]*Sqrt[1+c*x]/Sqrt[d+e*x^2]*Int[(d-c*d*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[p-1/2]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && PositiveIntegerQ[p]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(Sqrt[d]-Sqrt[-e]*x)^p*(Sqrt[d]+Sqrt[-e]*x)^p*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NegativeIntegerQ[p] && PositiveIntegerQ[n]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e*g*(p+1)) - 
  b*n/(2*c*Sqrt[d]*Sqrt[-f]*(p+1))*Int[(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[n] && n>0 && p!=-1


Int[x_^m_*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n/(m+1) - 
  b*c*Sqrt[d]*Sqrt[-f]*n/(m+1)*Int[x^(m+1)*(d+e*x)^(p-1/2)*(f+g*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] - 
  2*e*g*p/(m+1)*Int[x^(m+2)*(d+e*x)^(p-1)*(f+g*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[m,n] && n>0 && p>0 && m<-1


Int[x_^m_*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n/(m+2*p+1) - 
  b*c*n*Sqrt[d]*Sqrt[-f]/(m+2*p+1)*Int[x^(m+1)*(d+e*x)^(p-1/2)*(f+g*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] + 
  2*d*f*p/(m+2*p+1)*Int[x^m*(d+e*x)^(p-1)*(f+g*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[m,n] && n>0 && p>0 && m+2*p+1!=0


Int[x_^m_*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d*f*(m+1)) + 
  b*c*n/(Sqrt[d]*Sqrt[-f]*(m+1))*Int[x^(m+1)*(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[m,n] && n>0 && p<0 && m!=-1 && m+2*p+3==0


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_./((d_+e_.*x_)*(f_+g_.*x_)),x_Symbol] :=
  -1/(c^(m+1)*d)*Subst[Int[(a+b*x)^n*Cosh[x]^m*Csch[x],x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f] && PositiveIntegerQ[n] && IntegerQ[m] && m^2==1


Int[x_^m_*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x^(m-1)*(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(e*g*(m+2*p+1)) - 
  b*c*Sqrt[d]*Sqrt[-f]*n/(e*g*(m+2*p+1))*Int[x^(m-1)*(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] + 
  (m-1)/(c^2*(m+2*p+1))*Int[x^(m-2)*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[m,n] && n>0 && -1<=p<0 && m>1 && NonzeroQ[m+2*p+1]


Int[x_^m_*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x^(m-1)*(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e*g*(p+1)) - 
  b*n/(2*c*Sqrt[d]*Sqrt[-f]*(p+1))*Int[x^(m-1)*(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] - 
  (m-1)/(2*e*g*(p+1))*Int[x^(m-2)*(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[m,n] && n>0 && p<-1 && m>1


Int[ArcCosh[c_.*x_]/(x_*Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  -2*ArcCosh[c*x]*ArcTan[c*x-Sqrt[-1+c*x]*Sqrt[1+c*x]]/(Sqrt[d]*Sqrt[-f]) + 
  I*PolyLog[2,I*(c*x-Sqrt[-1+c*x]*Sqrt[1+c*x])]/(Sqrt[d]*Sqrt[-f]) - 
  I*PolyLog[2,I*(-c*x+Sqrt[-1+c*x]*Sqrt[1+c*x])]/(Sqrt[d]*Sqrt[-f]) /;
FreeQ[{c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f]


Int[(a_+b_.*ArcCosh[c_.*x_])/(x_*Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  a*Int[1/(x*Sqrt[d+e*x]*Sqrt[f+g*x]),x] + 
  b*Int[ArcCosh[c*x]/(x*Sqrt[d+e*x]*Sqrt[f+g*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_./x_,x_Symbol] :=
  c^2*Int[x*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x] + 
  1/(d*f)*Int[(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n/x,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[n] && n>0 && p<-1


Int[x_^m_*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d*f*(m+1)) + 
  b*c*n/(Sqrt[d]*Sqrt[-f]*(m+1))*Int[x^(m+1)*(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] + 
  c^2*(m+2*p+3)/(m+1)*Int[x^(m+2)*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[m,n] && n>0 && p<0 && m<-1 && m+2*p+3!=0


Int[x_^m_*(a_.+b_.*ArcCosh[c_.*x_])/(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  x^(m+1)*Sqrt[1-c^2*x^2]*(a+b*ArcCosh[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2]/((m+1)*Sqrt[d+e*x]*Sqrt[f+g*x]) + 
  b*c*x^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2]/(Sqrt[d]*Sqrt[-f]*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f] && Not[IntegerQ[m]]


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  x^m*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[d]*Sqrt[-f]*(n+1)) - 
  m/(b*c*Sqrt[d]*Sqrt[-f]*(n+1))*Int[x^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[d]*Sqrt[-f]*(n+1)) + 
  m*Sqrt[d]*Sqrt[-f]/(b*c*(n+1))*Int[x^(m-1)*(d+e*x)^(p-1/2)*(f+g*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[m,n] && n<-1 && m+2*p+1==0


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[d]*Sqrt[-f]*(n+1)) + 
  m*Sqrt[d]*Sqrt[-f]/(b*c*(n+1))*Int[x^(m-1)*(d+e*x)^(p-1/2)*(f+g*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] - 
  c*Sqrt[d]*Sqrt[-f]*(m+2*p+1)/(b*(n+1))*Int[x^(m+1)*(d+e*x)^(p-1/2)*(f+g*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && RationalQ[m,n] && n<-1


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  1/(d*f)*Int[x^m*(d+e*x)^(p+1)*(f+g*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] - 
  e*g/(d*f)*Int[x^(m+2)*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && NegativeIntegerQ[p+1/2] && PositiveQ[d] && NegativeQ[f] && NegativeIntegerQ[(m-1)/2]


Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  1/(c^(m+1)*Sqrt[d]*Sqrt[-f])*Subst[Int[(a+b*x)^n*Cosh[x]^m,x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f] && IntegerQ[m] && (m>0 || PositiveIntegerQ[n])


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  d^p*(-f)^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cosh[x]^m*Sinh[x]^(2*p+1),x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveIntegerQ[2*p] && PositiveQ[d] && NegativeQ[f] && PositiveIntegerQ[m]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n/(Sqrt[d+e*x]*Sqrt[f+g*x]),x^m*(d+e*x)^(p+1/2)*(f+g*x)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveIntegerQ[p+1/2] && PositiveQ[d] && NegativeQ[f] && Not[PositiveIntegerQ[(m+1)/2]]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  d^p*(-f)^p*Int[x^m*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && IntegerQ[p] && Not[PositiveQ[d] && NegativeQ[f]]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*(-f)^(p-1/2)*Sqrt[d+e*x]*Sqrt[f+g*x]/(Sqrt[1+c*x]*Sqrt[-1+c*x])*Int[x^m*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveIntegerQ[p+1/2] && Not[PositiveQ[d] && NegativeQ[f]]


Int[x_^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*(-f)^(p+1/2)*Sqrt[1+c*x]*Sqrt[-1+c*x]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[x^m*(1+c*x)^p*(-1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && NegativeIntegerQ[p-1/2] && Not[PositiveQ[d] && NegativeQ[f]]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])/(2*e*(p+1)) - 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcCosh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[x^m*(d-c*d*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d+e*x^2]/(Sqrt[d-c*d*x]*Sqrt[1+c*x])*Int[x^m*(d-c*d*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[p+1/2]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Sqrt[d-c*d*x]*Sqrt[1+c*x]/Sqrt[d+e*x^2]*Int[x^m*(d-c*d*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[p-1/2]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(h_.+i_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  (h+i*x)^m*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[d]*Sqrt[-f]*(n+1)) - 
  i*m/(b*c*Sqrt[d]*Sqrt[-f]*(n+1))*Int[(h+i*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f] && RationalQ[n] && n<-1


Int[(h_.+i_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  1/(c^(m+1)*Sqrt[d]*Sqrt[-f])*Subst[Int[(a+b*x)^n*(c*h+i*Cosh[x])^m,x],x,ArcCosh[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && PositiveQ[d] && NegativeQ[f] && IntegerQ[m]


Int[(h_.+i_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]),x_Symbol] :=
  Sqrt[-1+c*x]*Sqrt[1+c*x]/(Sqrt[d+e*x]*Sqrt[f+g*x])*Int[(h+i*x)^m*(a+b*ArcCosh[c*x])^n/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n},x] && ZeroQ[e-c*d] && ZeroQ[g+c*f] && Not[PositiveQ[d] && NegativeQ[f]]


Int[(i_*x_)^m_*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (i*x)^m/x^m*Int[x^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,i,m,n,p},x]


Int[(h_.+i_.*x_)^m_.*(d_+e_.*x_)^p_.*(f_+g_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(h+i*x)^m*(d+e*x)^p*(f+g*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n,p},x]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[d-c*d*x]*Sqrt[1+c*x]/Sqrt[d+e*x^2]*Int[(f+g*x)^m*(a+b*ArcCosh[c*x])^n/(Sqrt[d-c*d*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[c^2*d+e]


Int[(g_*x_)^m_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  (g*x)^m/x^m*Int[x^m*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,g,m,n,p},x]


Int[(f_.+g_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(f+g*x)^m*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


(* ::Subsection::Closed:: *)
(*u (a+b arctanh(c x))^n*)


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcTanh[c*x])^n -
  b*c*n*Int[x*(a+b*ArcTanh[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcCoth[c*x])^n -
  b*c*n*Int[x*(a+b*ArcCoth[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTanh[c*x])^n*Log[2*d/(d+e*x)]/e +
  b*c*n/e*Int[(a+b*ArcTanh[c*x])^(n-1)*Log[2*d/(d+e*x)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2-e^2] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCoth[c*x])^n*Log[2*d/(d+e*x)]/e +
  b*c*n/e*Int[(a+b*ArcCoth[c*x])^(n-1)*Log[2*d/(d+e*x)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2-e^2] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcTanh[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  a/e*Log[RemoveContent[d+e*x,x]] + b/2*Int[Log[1+c*x]/(d+e*x),x] - b/2*Int[Log[1-c*x]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(a_.+b_.*ArcCoth[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  a/e*Log[RemoveContent[d+e*x,x]] + b/2*Int[Log[1+1/(c*x)]/(d+e*x),x] - b/2*Int[Log[1-1/(c*x)]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  (d+e*x)^(p+1)*(a+b*ArcTanh[c*x])/(e*(p+1)) - 
  b*c/(e*(p+1))*Int[(d+e*x)^(p+1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  (d+e*x)^(p+1)*(a+b*ArcCoth[c*x])/(e*(p+1)) - 
  b*c/(e*(p+1))*Int[(d+e*x)^(p+1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_/x_,x_Symbol] :=
  2*(a+b*ArcTanh[c*x])^n*ArcTanh[1-2/(1-c*x)] -
  2*b*c*n*Int[(a+b*ArcTanh[c*x])^(n-1)*ArcTanh[1-2/(1-c*x)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_/x_,x_Symbol] :=
  2*(a+b*ArcCoth[c*x])^n*ArcCoth[1-2/(1-c*x)] -
  2*b*c*n*Int[(a+b*ArcCoth[c*x])^(n-1)*ArcCoth[1-2/(1-c*x)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcTanh[c*x])^n/(m+1) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcTanh[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,m},x] && IntegerQ[n] && n>1 && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcCoth[c*x])^n/(m+1) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCoth[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,m},x] && IntegerQ[n] && n>1 && NonzeroQ[m+1]


Int[(d_+e_.*x_)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(a+b*ArcTanh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[n,p]


Int[(d_+e_.*x_)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(a+b*ArcCoth[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[n,p]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[PositiveIntegerQ[n]]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[PositiveIntegerQ[n]]


Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/e*Int[x^(m-1)*(a+b*ArcTanh[c*x])^n,x] -
  d/e*Int[x^(m-1)*(a+b*ArcTanh[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2-e^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/e*Int[x^(m-1)*(a+b*ArcCoth[c*x])^n,x] -
  d/e*Int[x^(m-1)*(a+b*ArcCoth[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2-e^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcTanh[c*x])^n*Log[2*e*x/(d+e*x)]/d - 
  b*c*n/d*Int[(a+b*ArcTanh[c*x])^(n-1)*Log[2*e*x/(d+e*x)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2-e^2] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcCoth[c*x])^n*Log[2*e*x/(d+e*x)]/d -
  b*c*n/d*Int[(a+b*ArcCoth[c*x])^(n-1)*Log[2*e*x/(d+e*x)]/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2-e^2] && PositiveIntegerQ[n]


Int[x_^m_*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTanh[c*x])^n,x] -
  e/d*Int[x^(m+1)*(a+b*ArcTanh[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2-e^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCoth[c*x])^n,x] -
  e/d*Int[x^(m+1)*(a+b*ArcCoth[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d^2-e^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcTanh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || NonzeroQ[a] || IntegerQ[m])


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcCoth[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || NonzeroQ[a] || IntegerQ[m])


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^p/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcTanh[c*x])/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcTanh[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[p] && p>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^p/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcCoth[c*x])/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCoth[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[p] && p>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_,x_Symbol] :=
  b*n*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n-1)/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcTanh[c*x])^n,x] - 
  b^2*d*n*(n-1)/(2*p*(2*p+1))*Int[(d+e*x^2)^(p-1)*(a+b*ArcTanh[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n,p] && p>0 && n>1


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_,x_Symbol] :=
  b*n*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n-1)/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCoth[c*x])^n,x] - 
  b^2*d*n*(n-1)/(2*p*(2*p+1))*Int[(d+e*x^2)^(p-1)*(a+b*ArcCoth[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n,p] && p>0 && n>1


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcTanh[c_.*x_])),x_Symbol] :=
  Log[RemoveContent[a+b*ArcTanh[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCoth[c_.*x_])),x_Symbol] :=
  Log[RemoveContent[a+b*ArcCoth[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(n+1)/(b*c*d*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NonzeroQ[n+1]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(n+1)/(b*c*d*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NonzeroQ[n+1]


Int[(a_.+b_.*ArcTanh[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*(a+b*ArcTanh[c*x])*ArcTan[Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,-I*Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,I*Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(a_.+b_.*ArcCoth[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*(a+b*ArcCoth[c*x])*ArcTan[Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,-I*Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,I*Sqrt[1-c*x]/Sqrt[1+c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c*Sqrt[d])*Subst[Int[(a+b*x)^n*Sech[x],x],x,ArcTanh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -x*Sqrt[1-1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n*Csch[x],x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTanh[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCoth[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTanh[c*x])^n/(2*d*(d+e*x^2)) + 
  (a+b*ArcTanh[c*x])^(n+1)/(2*b*c*d^2*(n+1)) - 
  b*c*n/2*Int[x*(a+b*ArcTanh[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcCoth[c*x])^n/(2*d*(d+e*x^2)) + 
  (a+b*ArcCoth[c*x])^(n+1)/(2*b*c*d^2*(n+1)) - 
  b*c*n/2*Int[x*(a+b*ArcCoth[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcTanh[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTanh[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e]


Int[(a_.+b_.*ArcCoth[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCoth[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(p+1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[p] && p<-1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(p+1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[p] && p<-1 && p!=-3/2


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b*n*(a+b*ArcTanh[c*x])^(n-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTanh[c*x])^n/(d*Sqrt[d+e*x^2]) +
  b^2*n*(n-1)*Int[(a+b*ArcTanh[c*x])^(n-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>1


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b*n*(a+b*ArcCoth[c*x])^(n-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCoth[c*x])^n/(d*Sqrt[d+e*x^2]) +
  b^2*n*(n-1)*Int[(a+b*ArcCoth[c*x])^(n-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_,x_Symbol] :=
  -b*n*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^(n-1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^n/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^n,x] +
  b^2*n*(n-1)/(4*(p+1)^2)*Int[(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n,p] && p<-1 && n>1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_,x_Symbol] :=
  -b*n*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^(n-1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^n/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^n,x] +
  b^2*n*(n-1)/(4*(p+1)^2)*Int[(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n,p] && p<-1 && n>1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^(n+1)/(b*c*d*(n+1)) + 
  2*c*(p+1)/(b*(n+1))*Int[x*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n,p] && p<-1 && n<-1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^(n+1)/(b*c*d*(n+1)) + 
  2*c*(p+1)/(b*(n+1))*Int[x*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n,p] && p<-1 && n<-1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  d^p/c*Subst[Int[(a+b*x)^n/Cosh[x]^(2*(p+1)),x],x,ArcTanh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[2*(p+1)] && (IntegerQ[p] || PositiveQ[d])


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[2*(p+1)] && Not[IntegerQ[p] || PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  -(-d)^p/c*Subst[Int[(a+b*x)^n/Sinh[x]^(2*(p+1)),x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[2*(p+1)] && IntegerQ[p]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  -(-d)^(p+1/2)*x*Sqrt[(c^2*x^2-1)/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n/Sinh[x]^(2*(p+1)),x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && NegativeIntegerQ[2*(p+1)] && Not[IntegerQ[p]]


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


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcTanh[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcCoth[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcTanh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcCoth[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_^m_*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcTanh[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcTanh[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcCoth[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcCoth[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTanh[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcTanh[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCoth[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcCoth[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m<-1


Int[x_*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(n+1)/(b*e*(n+1)) + 
  1/(c*d)*Int[(a+b*ArcTanh[c*x])^n/(1-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n]


Int[x_*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(n+1)/(b*e*(n+1)) + 
  1/(c*d)*Int[(a+b*ArcCoth[c*x])^n/(1-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n]


Int[x_*(a_.+b_.*ArcTanh[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  x*(a+b*ArcTanh[c*x])^(n+1)/(b*c*d*(n+1)) - 
  1/(b*c*d*(n+1))*Int[(a+b*ArcTanh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && Not[PositiveIntegerQ[n]] && NonzeroQ[n+1]


Int[x_*(a_.+b_.*ArcCoth[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  -x*(a+b*ArcCoth[c*x])^(n+1)/(b*c*d*(n+1)) - 
  1/(b*c*d*(n+1))*Int[(a+b*ArcCoth[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && Not[PositiveIntegerQ[n]] && NonzeroQ[n+1]


Int[x_^m_*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcTanh[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcTanh[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcCoth[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcCoth[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(n+1)/(b*d*(n+1)) +
  1/d*Int[(a+b*ArcTanh[c*x])^n/(x*(1+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(n+1)/(b*d*(n+1)) +
  1/d*Int[(a+b*ArcCoth[c*x])^n/(x*(1+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0


Int[x_^m_*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTanh[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcTanh[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCoth[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcCoth[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcTanh[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  x^m*(a+b*ArcTanh[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*d*(n+1))*Int[x^(m-1)*(a+b*ArcTanh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n<-1


Int[x_^m_*(a_.+b_.*ArcCoth[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  x^m*(a+b*ArcCoth[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*d*(n+1))*Int[x^(m-1)*(a+b*ArcCoth[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n<-1


Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTanh[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[m==1 && NonzeroQ[a]]


Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCoth[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[m==1 && NonzeroQ[a]]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^n/(2*e*(p+1)) + 
  b*n/(2*c*(p+1))*Int[(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && NonzeroQ[p+1]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^n/(2*e*(p+1)) +
  b*n/(2*c*(p+1))*Int[(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && NonzeroQ[p+1]


Int[x_*(a_.+b_.*ArcTanh[c_.*x_])^n_/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTanh[c*x])^(n+1)/(b*c*d*(n+1)*(d+e*x^2)) +
  (1+c^2*x^2)*(a+b*ArcTanh[c*x])^(n+2)/(b^2*e*(n+1)*(n+2)*(d+e*x^2)) +
  4/(b^2*(n+1)*(n+2))*Int[x*(a+b*ArcTanh[c*x])^(n+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n<-1 && n!=-2


Int[x_*(a_.+b_.*ArcCoth[c_.*x_])^n_/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcCoth[c*x])^(n+1)/(b*c*d*(n+1)*(d+e*x^2)) +
  (1+c^2*x^2)*(a+b*ArcCoth[c*x])^(n+2)/(b^2*e*(n+1)*(n+2)*(d+e*x^2)) +
  4/(b^2*(n+1)*(n+2))*Int[x*(a+b*ArcCoth[c*x])^(n+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n<-1 && n!=-2


Int[x_^2*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(p+1)/(4*c^3*d*(p+1)^2) - 
  x*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])/(2*c^2*d*(p+1)) + 
  1/(2*c^2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[p] && p<-1 && p!=-5/2


Int[x_^2*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(p+1)/(4*c^3*d*(p+1)^2) - 
  x*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])/(2*c^2*d*(p+1)) + 
  1/(2*c^2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[p] && p<-1 && p!=-5/2


Int[x_^2*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  -(a+b*ArcTanh[c*x])^(n+1)/(2*b*c^3*d^2*(n+1)) + 
  x*(a+b*ArcTanh[c*x])^n/(2*c^2*d*(d+e*x^2)) - 
  b*n/(2*c)*Int[x*(a+b*ArcTanh[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0


Int[x_^2*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  -(a+b*ArcCoth[c*x])^(n+1)/(2*b*c^3*d^2*(n+1)) + 
  x*(a+b*ArcCoth[c*x])^n/(2*c^2*d*(d+e*x^2)) - 
  b*n/(2*c)*Int[x*(a+b*ArcCoth[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  -b*x^m*(d+e*x^2)^(p+1)/(c*d*m^2) + 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])/(c^2*d*m) - 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && ZeroQ[m+2*p+2] && RationalQ[p] && p<-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  -b*x^m*(d+e*x^2)^(p+1)/(c*d*m^2) + 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])/(c^2*d*m) - 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && ZeroQ[m+2*p+2] && RationalQ[p] && p<-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_,x_Symbol] :=
  -b*n*x^m*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^(n-1)/(c*d*m^2) + 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^n/(c^2*d*m) + 
  b^2*n*(n-1)/m^2*Int[x^m*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n-2),x] - 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && ZeroQ[m+2*p+2] && RationalQ[n,p] && p<-1 && n>1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_,x_Symbol] :=
  -b*n*x^m*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^(n-1)/(c*d*m^2) + 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^n/(c^2*d*m) + 
  b^2*n*(n-1)/m^2*Int[x^m*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n-2),x] - 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && ZeroQ[m+2*p+2] && RationalQ[n,p] && p<-1 && n>1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[c^2*d+e] && ZeroQ[m+2*p+2] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[c^2*d+e] && ZeroQ[m+2*p+2] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^n/(d*(m+1)) - 
  b*c*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[c^2*d+e] && ZeroQ[m+2*p+3] && RationalQ[n] && n>0 && NonzeroQ[m+1]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^n/(d*(m+1)) - 
  b*c*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[c^2*d+e] && ZeroQ[m+2*p+3] && RationalQ[n] && n>0 && NonzeroQ[m+1]


Int[x_^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTanh[c*x])/(m+2) - 
  b*c*d/(m+2)*Int[x^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[x^m*(a+b*ArcTanh[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && NonzeroQ[m+2]


Int[x_^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCoth[c*x])/(m+2) - 
  b*c*d/(m+2)*Int[x^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[x^m*(a+b*ArcCoth[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && NonzeroQ[m+2]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  d*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcTanh[c*x])^n,x] - 
  c^2*d*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && RationalQ[p] && p>0 && PositiveIntegerQ[n] && (RationalQ[m] || OneQ[n] && IntegerQ[p])


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  d*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcCoth[c*x])^n,x] - 
  c^2*d*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[c^2*d+e] && RationalQ[p] && p>0 && PositiveIntegerQ[n] && (RationalQ[m] || OneQ[n] && IntegerQ[p])


Int[x_^m_*(a_.+b_.*ArcTanh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -x^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcTanh[c*x])^n/(c^2*d*m) + 
  b*n/(c*m)*Int[x^(m-1)*(a+b*ArcTanh[c*x])^(n-1)/Sqrt[d+e*x^2],x] + 
  (m-1)/(c^2*m)*Int[x^(m-2)*(a+b*ArcTanh[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCoth[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -x^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCoth[c*x])^n/(c^2*d*m) + 
  b*n/(c*m)*Int[x^(m-1)*(a+b*ArcCoth[c*x])^(n-1)/Sqrt[d+e*x^2],x] + 
  (m-1)/(c^2*m)*Int[x^(m-2)*(a+b*ArcCoth[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1


Int[(a_.+b_.*ArcTanh[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcTanh[c*x])*ArcTanh[Sqrt[1-c*x]/Sqrt[1+c*x]] + 
  b/Sqrt[d]*PolyLog[2,-Sqrt[1-c*x]/Sqrt[1+c*x]] - 
  b/Sqrt[d]*PolyLog[2,Sqrt[1-c*x]/Sqrt[1+c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(a_.+b_.*ArcCoth[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcCoth[c*x])*ArcTanh[Sqrt[1-c*x]/Sqrt[1+c*x]] + 
  b/Sqrt[d]*PolyLog[2,-Sqrt[1-c*x]/Sqrt[1+c*x]] - 
  b/Sqrt[d]*PolyLog[2,Sqrt[1-c*x]/Sqrt[1+c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveQ[d]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  1/Sqrt[d]*Subst[Int[(a+b*x)^n*Csch[x],x],x,ArcTanh[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -c*x*Sqrt[1-1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n*Sech[x],x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTanh[c*x])^n/(x*Sqrt[1-c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCoth[c*x])^n/(x*Sqrt[1-c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcTanh[c*x])^n/(d*x) + 
  b*c*n*Int[(a+b*ArcTanh[c*x])^(n-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcCoth[c*x])^n/(d*x) + 
  b*c*n*Int[(a+b*ArcCoth[c*x])^(n-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0


Int[x_^m_*(a_.+b_.*ArcTanh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTanh[c*x])^n/(d*(m+1)) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcTanh[c*x])^(n-1)/Sqrt[d+e*x^2],x] + 
  c^2*(m+2)/(m+1)*Int[x^(m+2)*(a+b*ArcTanh[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_^m_*(a_.+b_.*ArcCoth[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCoth[c*x])^n/(d*(m+1)) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCoth[c*x])^(n-1)/Sqrt[d+e*x^2],x] + 
  c^2*(m+2)/(m+1)*Int[x^(m+2)*(a+b*ArcCoth[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^n,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^n,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^n,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^n,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n+1),x] + 
  c*(m+2*p+2)/(b*(n+1))*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n,p] && p<-1 && n<-1 && NonzeroQ[m+2*p+2]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n+1),x] + 
  c*(m+2*p+2)/(b*(n+1))*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[m,n,p] && p<-1 && n<-1 && NonzeroQ[m+2*p+2]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Sinh[x]^m/Cosh[x]^(m+2*(p+1)),x],x,ArcTanh[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && (IntegerQ[p] || PositiveQ[d])


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && Not[IntegerQ[p] || PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  -(-d)^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cosh[x]^m/Sinh[x]^(m+2*(p+1)),x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  -(-d)^(p+1/2)*x*Sqrt[(c^2*x^2-1)/(c^2*x^2)]/(c^m*Sqrt[d+e*x^2])*Subst[Int[(a+b*x)^n*Cosh[x]^m/Sinh[x]^(m+2*(p+1)),x],x,ArcCoth[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && Not[IntegerQ[p]]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTanh[c*x])/(2*e*(p+1)) - 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCoth[c*x])/(2*e*(p+1)) - 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcTanh[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[a+b*ArcCoth[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTanh[c*x])^n,x^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || p<-1 && IntegerQ[m] && m!=1)


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCoth[c*x])^n,x^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || p<-1 && IntegerQ[m] && m!=1)


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
  a*Int[x^m*(d+e*x^2)^p,x] + b*Int[x^m*(d+e*x^2)^p*ArcTanh[c*x],x] /;
FreeQ[{a,b,c,d,e,m,p},x]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
  a*Int[x^m*(d+e*x^2)^p,x] + b*Int[x^m*(d+e*x^2)^p*ArcCoth[c*x],x] /;
FreeQ[{a,b,c,d,e,m,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcTanh[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcCoth[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[ArcTanh[u_]*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTanh[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTanh[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+c*x))^2]


Int[ArcCoth[u_]*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCoth[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCoth[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+c*x))^2]


Int[ArcTanh[u_]*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTanh[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTanh[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-c*x))^2]


Int[ArcCoth[u_]*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCoth[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCoth[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-c*x))^2]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) -
  b*n/2*Int[(a+b*ArcTanh[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1+c*x))^2]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) -
  b*n/2*Int[(a+b*ArcCoth[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1+c*x))^2]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcTanh[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) +
  b*n/2*Int[(a+b*ArcTanh[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1-c*x))^2]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCoth[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) +
  b*n/2*Int[(a+b*ArcCoth[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1-c*x))^2]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcTanh[c*x])^n*PolyLog[p+1,u]/(2*c*d) +
  b*n/2*Int[(a+b*ArcTanh[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+c*x))^2]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCoth[c*x])^n*PolyLog[p+1,u]/(2*c*d) +
  b*n/2*Int[(a+b*ArcCoth[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+c*x))^2]


Int[(a_.+b_.*ArcTanh[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^n*PolyLog[p+1,u]/(2*c*d) -
  b*n/2*Int[(a+b*ArcTanh[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-c*x))^2]


Int[(a_.+b_.*ArcCoth[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^n*PolyLog[p+1,u]/(2*c*d) -
  b*n/2*Int[(a+b*ArcCoth[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[c^2*d+e] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-c*x))^2]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCoth[c_.*x_])*(a_.+b_.*ArcTanh[c_.*x_])),x_Symbol] :=
  (-Log[a+b*ArcCoth[c*x]]+Log[a+b*ArcTanh[c*x]])/(b^2*c*d*(ArcCoth[c*x]-ArcTanh[c*x])) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e]


Int[(a_.+b_.*ArcCoth[c_.*x_])^m_.*(a_.+b_.*ArcTanh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcCoth[c*x])^(m+1)*(a+b*ArcTanh[c*x])^n/(b*c*d*(m+1)) -
  n/(m+1)*Int[(a+b*ArcCoth[c*x])^(m+1)*(a+b*ArcTanh[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegersQ[m,n] && 0<n<=m


Int[(a_.+b_.*ArcTanh[c_.*x_])^m_.*(a_.+b_.*ArcCoth[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTanh[c*x])^(m+1)*(a+b*ArcCoth[c*x])^n/(b*c*d*(m+1)) -
  n/(m+1)*Int[(a+b*ArcTanh[c*x])^(m+1)*(a+b*ArcCoth[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c^2*d+e] && IntegersQ[m,n] && 0<n<m


Int[ArcTanh[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+a*x]/(c+d*x^n),x] -
  1/2*Int[Log[1-a*x]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[a^2*c+d]]


Int[ArcCoth[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+1/(a*x)]/(c+d*x^n),x] -
  1/2*Int[Log[1-1/(a*x)]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[a^2*c+d]]


Int[(a_.+b_.*ArcTanh[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  x*(a+b*ArcTanh[c*x])*(d+e*Log[f+g*x^2]) - 
  2*e*g*Int[x^2*(a+b*ArcTanh[c*x])/(f+g*x^2),x] - 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[(a_.+b_.*ArcCoth[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  x*(a+b*ArcCoth[c*x])*(d+e*Log[f+g*x^2]) - 
  2*e*g*Int[x^2*(a+b*ArcCoth[c*x])/(f+g*x^2),x] - 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  x^(m+1)*(a+b*ArcTanh[c*x])*(d+e*Log[f+g*x^2])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcTanh[c*x])/(f+g*x^2),x] - 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[m/2]


Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  x^(m+1)*(a+b*ArcCoth[c*x])*(d+e*Log[f+g*x^2])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcCoth[c*x])/(f+g*x^2),x] - 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[m/2]


Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*Log[f+g*x^2]),x]]},  
  Dist[a+b*ArcTanh[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[(m+1)/2]


Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*Log[f+g*x^2]),x]]},  
  Dist[a+b*ArcCoth[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1-c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[(m+1)/2]


Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(a+b*ArcTanh[c*x]),x]]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && m!=-1


Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_])*(d_.+e_.*Log[f_.+g_.*x_^2]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(a+b*ArcCoth[c*x]),x]]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && m!=-1


Int[x_*(a_.+b_.*ArcTanh[c_.*x_])^2*(d_.+e_.*Log[f_+g_.*x_^2]),x_Symbol] :=
  (f+g*x^2)*(a+b*ArcTanh[c*x])^2*(d+e*Log[f+g*x^2])/(2*g) - 
  e*x^2*(a+b*ArcTanh[c*x])^2/2 + 
  b/c*Int[(a+b*ArcTanh[c*x])*(d+e*Log[f+g*x^2]),x] + 
  b*c*e*Int[x^2*(a+b*ArcTanh[c*x])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[c^2*f+g]


Int[x_*(a_.+b_.*ArcCoth[c_.*x_])^2*(d_.+e_.*Log[f_+g_.*x_^2]),x_Symbol] :=
  (f+g*x^2)*(a+b*ArcCoth[c*x])^2*(d+e*Log[f+g*x^2])/(2*g) - 
  e*x^2*(a+b*ArcCoth[c*x])^2/2 + 
  b/c*Int[(a+b*ArcCoth[c*x])*(d+e*Log[f+g*x^2]),x] + 
  b*c*e*Int[x^2*(a+b*ArcCoth[c*x])/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[c^2*f+g]


Int[(a_.+b_.*ArcTanh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcTanh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCoth[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCoth[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcTanh[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcTanh[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcCoth[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcCoth[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[PositiveIntegerQ[n]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcTanh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && PositiveIntegerQ[n]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCoth[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && PositiveIntegerQ[n]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcTanh[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcTanh[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[PositiveIntegerQ[n]]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCoth[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcCoth[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[PositiveIntegerQ[n]]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcTanh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^p*(a+b*ArcCoth[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcTanh[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCoth[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && ZeroQ[B*(1-c^2)+2*A*c*d] && ZeroQ[2*c*C-B*d]


(* ::Subsection::Closed:: *)
(*Inverse Hyperbolic Sine Functions*)


Int[ArcSinh[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Coth[x],x],x,ArcSinh[a*x^p]] /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0


Int[ArcCosh[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Tanh[x],x],x,ArcCosh[a*x^p]] /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0


Int[u_.*ArcSinh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCsch[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCosh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSech[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[f_^(c_.*ArcSinh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[f^(c*x^n)*Cosh[x],x],x,ArcSinh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[f_^(c_.*ArcCosh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[f^(c*x^n)*Sinh[x],x],x,ArcCosh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[x_^m_.*f_^(c_.*ArcSinh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[(-a/b+Sinh[x]/b)^m*f^(c*x^n)*Cosh[x],x],x,ArcSinh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[m,n]


Int[x_^m_.*f_^(c_.*ArcCosh[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[(-a/b+Cosh[x]/b)^m*f^(c*x^n)*Sinh[x],x],x,ArcCosh[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[m,n]


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
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCosh[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCosh[u])/(d*(m+1)) -
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSinh[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcSinh[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1+u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCosh[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
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
(*Inverse Hyperbolic Tangent Functions*)


Int[ArcTanh[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[1+a+b*x]/(c+d*x^n),x] -
  1/2*Int[Log[1-a-b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcCoth[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  1/2*Int[Log[(1+a+b*x)/(a+b*x)]/(c+d*x^n),x] -
  1/2*Int[Log[(-1+a+b*x)/(a+b*x)]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcTanh[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcTanh[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcCoth[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcCoth[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


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
FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n


Int[x_^m_.*ArcCoth[a_+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*ArcCoth[a+b*x^n]/(m+1) - 
  b*n/(m+1)*Int[x^(m+n)/(1-a^2-2*a*b*x^n-b^2*x^(2*n)),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n


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
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0


Int[x_^m_.*ArcCoth[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  1/2*Int[x^m*Log[1+1/(a+b*f^(c+d*x))],x] - 
  1/2*Int[x^m*Log[1-1/(a+b*f^(c+d*x))],x] /;
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0


Int[u_.*ArcTanh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCoth[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCoth[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcTanh[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  1/c*Log[ArcTanh[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && ZeroQ[b-c^2]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  -1/c*Log[ArcCoth[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && ZeroQ[b-c^2]


Int[ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  ArcTanh[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && ZeroQ[b-c^2] && NonzeroQ[m+1]


Int[ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  -ArcCoth[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && ZeroQ[b-c^2] && NonzeroQ[m+1]


Int[ArcTanh[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcTanh[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b-c^2] && ZeroQ[b*d-a*e]


Int[ArcCoth[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcCoth[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b-c^2] && ZeroQ[b*d-a*e]


Int[E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[((1+a*x)^((n+1)/2)/((1-a*x)^((n-1)/2)*Sqrt[1-a^2*x^2])),x] /;
FreeQ[a,x] && OddQ[n]


Int[x_^m_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[x^m*((1+a*x)^((n+1)/2)/((1-a*x)^((n-1)/2)*Sqrt[1-a^2*x^2])),x] /;
FreeQ[{a,m},x] && OddQ[n]


Int[E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,n},x] && Not[OddQ[n]]


Int[x_^m_.*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[x^m*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,m,n},x] && Not[OddQ[n]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1+d*x/c)^p*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2-d^2] && (IntegerQ[p] || PositiveQ[c])


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[u*(c+d*x)^p*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2-d^2] && Not[IntegerQ[p] || PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  d^p*Int[u*(1+c*x/d)^p*E^(n*ArcTanh[a*x])/x^p,x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[c^2-a^2*d^2] && IntegerQ[p]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*c^p*Int[u*(1+d/(c*x))^p*(1+1/(a*x))^(n/2)/(1-1/(a*x))^(n/2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  Int[u*(c+d/x)^p*(1+a*x)^(n/2)/(1-a*x)^(n/2),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  x^p*(c+d/x)^p/(1+c*x/d)^p*Int[u*(1+c*x/d)^p*E^(n*ArcTanh[a*x])/x^p,x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[p]]


Int[E^(n_.*ArcTanh[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcTanh[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]]


Int[E^(n_.*ArcTanh[a_.*x_])/Sqrt[1+d_.*x_^2],x_Symbol] :=
  Int[1/(1-a*n*x),x] /;
FreeQ[{a,d,n},x] && ZeroQ[d+a^2] && ZeroQ[n^2-1]


Int[E^(n_.*ArcTanh[a_.*x_])/Sqrt[c_.+d_.*x_^2],x_Symbol] :=
  Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[E^(n*ArcTanh[a*x])/Sqrt[1-a^2*x^2],x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-1] && NonzeroQ[c-1]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*a*p*x)*(c+d*x^2)^p*E^(n*ArcTanh[a*x])/(2*a*p*(2*p+1)) /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-4*p^2] && NonzeroQ[p+1/2] && Not[IntegerQ[n]]


(* Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*a*p*x)*(c+d*x^2)^p*E^(n*ArcTanh[a*x])/(2*a*p*(2*p+1)) - 
  c*(n^2-4*p^2)/(2*p*(2*p+1))*Int[(c+d*x^2)^(p-1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n^2-4*p^2] && RationalQ[p] && p>0 *)


Int[E^(n_.*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  1/c^(3/2)*Int[1/((1+a*n*x)*(1-a*n*x)^2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-1] && PositiveQ[c]


Int[E^(n_.*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  Sqrt[1-a^2*x^2]/(c*Sqrt[c+d*x^2])*Int[E^(n*ArcTanh[a*x])/(1-a^2*x^2)^(3/2),x] /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-1] && Not[PositiveQ[c]]


Int[E^(n_*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n-a*x)*E^(n*ArcTanh[a*x])/(a*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n^2-9] && NonzeroQ[n^2-1]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a*c*(n^2-4*(p+1)^2)) - 
  2*(p+1)*(2*p+3)/(c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n^2-4*p^2] && RationalQ[p] && p<-1 && p!=-3/2 && NonzeroQ[n^2-4*(p+1)^2] && 
  Not[IntegerQ[n]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-a^2*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c]) && OddQ[n]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c]) && Not[OddQ[n]] && 
  (RationalQ[n,p] || PositiveIntegerQ[p-n/2] || PositiveIntegerQ[p+n/2])


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(n/2)*Int[(c+d*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[p] || PositiveQ[c]] && EvenQ[n] && RationalQ[p]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && PositiveIntegerQ[p+1/2] && RationalQ[n]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && NegativeIntegerQ[p-1/2] && RationalQ[n]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(1-a^2*x^2)^p*Int[(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[p+1/2]] && 
  (RationalQ[n,p] || PositiveIntegerQ[p-n/2] || PositiveIntegerQ[p+n/2])


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(2*a*c*n)*(1+E^(n/(p+1)*ArcTanh[a*x]))^(2*(p+1))*
    Hypergeometric2F1[2*(p+1),2*(p+1),2*p+3,-E^(n/(p+1)*ArcTanh[a*x])] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2-4*(p+1)^2] && Not[IntegerQ[2*p]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  4^(p+1)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a*c*(n-2*(p+1)))*(1/(1+a*x))^(2*(p+1))*
    Hypergeometric2F1[p-n/2+1,2*(p+1),p-n/2+2,-E^(-2*ArcTanh[a*x])] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && NonzeroQ[n^2-4*(p+1)^2] && Not[NegativeIntegerQ[2*p+1]] && Not[IntegerQ[p-n/2]]


Int[x_*E^(n_*ArcTanh[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcTanh[a*x])/(a^2*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a^2*c*(n^2-4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p<=-1 && p!=-3/2 && NonzeroQ[n^2-4*(p+1)^2] && Not[IntegerQ[n]]


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  -(n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a^3*c*n^2*(n^2-1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && ZeroQ[n^2+2*(p+1)] && Not[IntegerQ[n]]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x])/(a^3*c*(n^2-4*(p+1)^2)) - 
  (n^2+2*(p+1))/(a^2*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && RationalQ[p] && p<=-1 && NonzeroQ[n^2+2*(p+1)] && NonzeroQ[n^2-4*(p+1)^2] && Not[IntegerQ[n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p/a^(m+1)*Subst[Int[E^(n*x)*Tanh[x]^(m+2*(p+1))/Sinh[x]^(2*(p+1)),x],x,ArcTanh[a*x]] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && IntegerQ[m] && RationalQ[p] && 3<=m<=-2(p+1) && IntegerQ[p] && Not[IntegerQ[n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c]) && ZeroQ[n^2-1] && 
  (Not[RationalQ[m]] || Not[RationalQ[p]]) && Not[IntegerQ[p-n/2]]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1-a^2*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c]) && OddQ[n] && 
  (Not[RationalQ[m]] || Not[RationalQ[p]] || ZeroQ[n-1] && NonzeroQ[p+1]) && Not[IntegerQ[p-n/2]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(n/2)*Int[x^m*(c+d*x^2)^(p-n/2)*(1+a*x)^n,x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[p] || PositiveQ[c]] && IntegerQ[n/2] && (ZeroQ[m-1] || Not[IntegerQ[p+1/2]])


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && (IntegerQ[p] || PositiveQ[c])


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/(Sqrt[1-a*x]*Sqrt[1+a*x])*Int[u*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && IntegerQ[n/2] && PositiveIntegerQ[p+1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1-a*x]*Sqrt[1+a*x]/Sqrt[c+d*x^2]*Int[u*(1-a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && IntegerQ[n/2] && NegativeIntegerQ[p-1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[u*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && Not[IntegerQ[n/2]] && PositiveIntegerQ[p+1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  c^(p+1/2)*Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[u*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]] && Not[IntegerQ[n/2]] && NegativeIntegerQ[p-1/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(1-a^2*x^2)^p*Int[u*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[n/2]] && Not[IntegerQ[p+1/2]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^(2*p)*(1-a^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[c+a^2*d] && IntegerQ[p]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-1/(a*x))^p*(1+1/(a*x))^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[p]] && IntegerQ[n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/((1-a*x)^p*(1+a*x)^p)*Int[u/x^(2*p)*(1-a*x)^p*(1+a*x)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[p]] && IntegerQ[n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcTanh[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/(1+c*x^2/d)^p*Int[u/x^(2*p)*(1+c*x^2/d)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[p]] && Not[IntegerQ[n/2]]


Int[u_.*E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*Int[u*E^(n*ArcTanh[a*x]),x] /;
FreeQ[a,x] && IntegerQ[n/2]


Int[E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^((n+1)/2)/(x^2*(1-x/a)^((n-1)/2)*Sqrt[1-x^2/a^2]),x],x,1/x] /;
FreeQ[a,x] && OddQ[n]


Int[x_^m_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^((n+1)/2)/(x^(m+2)*(1-x/a)^((n-1)/2)*Sqrt[1-x^2/a^2]),x],x,1/x] /;
FreeQ[a,x] && OddQ[n] && IntegerQ[m]


Int[E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^(n/2)/(x^2*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[n]]


Int[x_^m_.*E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[x_^m_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -x^m*(1/x)^m*Subst[Int[(1+x/a)^((n+1)/2)/(x^(m+2)*(1-x/a)^((n-1)/2)*Sqrt[1-x^2/a^2]),x],x,1/x] /;
FreeQ[{a,m},x] && OddQ[n] && Not[IntegerQ[m]]


Int[x_^m_*E^(n_*ArcCoth[a_.*x_]),x_Symbol] :=
  -x^m*(1/x)^m*Subst[Int[(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[n]] && Not[IntegerQ[m]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c^2-d^2] && Not[IntegerQ[n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(x^p*(1+c/(d*x))^p)*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c^2-d^2] && Not[IntegerQ[n/2]] && Not[IntegerQ[p]]


Int[(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^2*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c])


Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegerQ[m]


Int[x_^m_*(c_+d_./x_)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1+d*x/c)^p*(1+x/a)^(n/2)/(x^(m+2)*(1-x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[u*(1+d/(c*x))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c^2-a^2*d^2] && Not[IntegerQ[n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcCoth[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcCoth[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]]


Int[E^(n_*ArcCoth[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n-a*x)*E^(n*ArcCoth[a*x])/(a*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a*c*(n^2-4*(p+1)^2)) - 
  2*(p+1)*(2*p+3)/(c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && RationalQ[p] && p<-1 && p!=-3/2 && NonzeroQ[n^2-4*(p+1)^2] && 
  (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_*E^(n_*ArcCoth[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcCoth[a*x])/(a^2*c*(n^2-1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^2*c*(n^2-4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && RationalQ[p] && p<=-1 && p!=-3/2 && NonzeroQ[n^2-4*(p+1)^2] && 
  (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^3*c*n^2*(n^2-1)) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && ZeroQ[n^2+2*(p+1)] && NonzeroQ[n^2-1]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x])/(a^3*c*(n^2-4*(p+1)^2)) - 
  (n^2+2*(p+1))/(a^2*c*(n^2-4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && RationalQ[p] && p<=-1 && NonzeroQ[n^2+2*(p+1)] && 
  NonzeroQ[n^2-4*(p+1)^2] && (IntegerQ[p] || Not[IntegerQ[n]])


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -(-c)^p/a^(m+1)*Subst[Int[E^(n*x)*Coth[x]^(m+2*(p+1))/Cosh[x]^(2*(p+1)),x],x,ArcCoth[a*x]] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && IntegerQ[m] && RationalQ[p] && 3<=m<=-2(p+1) && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^(2*p)*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(x^(2*p)*(1-1/(a^2*x^2))^p)*Int[u*x^(2*p)*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[a^2*c+d] && Not[IntegerQ[n/2]] && Not[IntegerQ[p]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  c^p/a^(2*p)*Int[u/x^(2*p)*(-1+a*x)^(p-n/2)*(1+a*x)^(p+n/2),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegersQ[2*p,p+n/2]


Int[(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^2,x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+n/2]]


Int[x_^m_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+n/2]] && 
  IntegerQ[m]


Int[x_^m_*(c_+d_./x_^2)^p_.*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1-x/a)^(p-n/2)*(1+x/a)^(p+n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+n/2]] && 
  Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcCoth[a_.*x_]),x_Symbol] :=
  (c+d/x^2)^p/(1-1/(a^2*x^2))^p*Int[u*(1-1/(a^2*x^2))^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && ZeroQ[c+a^2*d] && Not[IntegerQ[n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(1+a*c+b*c*x)^(n/2)/(1-a*c-b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,n},x]


Int[x_^m_*E^(n_*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/n)*(-1-a*c+(1-a*c)*x^(2/n))^m/(1+x^(2/n))^(m+2),x],x,(1+c*(a+b*x))^(n/2)/(1-c*(a+b*x))^(n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[n] && -1<n<1


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcTanh[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(d+e*x)^m*(1+a*c+b*c*x)^(n/2)/(1-a*c-b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTanh[a_+b_.*x_]),x_Symbol] :=
  (c/(1-a^2))^p*Int[u*(1-a-b*x)^(p-n/2)*(1+a+b*x)^(p+n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c+e(1-a^2)] && (IntegerQ[p] || PositiveQ[c/(1-a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTanh[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1-a^2-2*a*b*x-b^2*x^2)^p*Int[u*(1-a^2-2*a*b*x-b^2*x^2)^p*E^(n*ArcTanh[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c+e(1-a^2)] && Not[IntegerQ[p] || PositiveQ[c/(1-a^2)]]


Int[u_.*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (-1)^(n/2)*Int[u*E^(n*ArcTanh[c*(a+b*x)]),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n/2]


Int[E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (c*(a+b*x))^(n/2)*(1+1/(c*(a+b*x)))^(n/2)/(1+a*c+b*c*x)^(n/2)*Int[(1+a*c+b*c*x)^(n/2)/(-1+a*c+b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[n/2]]


Int[x_^m_*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  -4/(n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/n)*(1+a*c+(1-a*c)*x^(2/n))^m/(-1+x^(2/n))^(m+2),x],x,(1+1/(c*(a+b*x)))^(n/2)/(1-1/(c*(a+b*x)))^(n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[n] && -1<n<1


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (c*(a+b*x))^(n/2)*(1+1/(c*(a+b*x)))^(n/2)/(1+a*c+b*c*x)^(n/2)*Int[(d+e*x)^m*(1+a*c+b*c*x)^(n/2)/(-1+a*c+b*c*x)^(n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[n/2]]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCoth[a_+b_.*x_]),x_Symbol] :=
  (c/(1-a^2))^p*((a+b*x)/(1+a+b*x))^(n/2)*((1+a+b*x)/(a+b*x))^(n/2)*((1-a-b*x)^(n/2)/(-1+a+b*x)^(n/2))*
    Int[u*(1-a-b*x)^(p-n/2)*(1+a+b*x)^(p+n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[n/2]] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c+e(1-a^2)] && (IntegerQ[p] || PositiveQ[c/(1-a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCoth[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1-a^2-2*a*b*x-b^2*x^2)^p*Int[u*(1-a^2-2*a*b*x-b^2*x^2)^p*E^(n*ArcCoth[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[n/2]] && ZeroQ[b*d-2*a*e] && ZeroQ[b^2*c+e(1-a^2)] && 
  Not[IntegerQ[p] || PositiveQ[c/(1-a^2)]]


Int[u_.*E^(n_.*ArcTanh[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcCoth[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*E^(n_.*ArcCoth[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcTanh[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[(c_.+d_.*x_^2)^n_*ArcTanh[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcTanh[a*x],u,x] - 
  a*Int[Dist[1/(1-a^2*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[2*n] && n<=-1


Int[(c_.+d_.*x_^2)^n_*ArcCoth[a_.*x_],x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(c+d*x^2)^n,x]]},  
  Dist[ArcCoth[a*x],u,x] - 
  a*Int[Dist[1/(1-a^2*x^2),u,x],x]] /;
FreeQ[{a,c,d},x] && IntegerQ[2*n] && n<=-1


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcTanh[a+b*x]]/(1-(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Tanh[x]/b,x],x],x,ArcTanh[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sech[x]^(2*(n+1)),x],x], x, tmp]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTanh && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sech[x]^(2*(n+1)),x],x], x, tmp] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTanh && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcCoth[a+b*x]]/(1-(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Coth[x]/b,x],x],x,ArcCoth[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*(-Csch[x]^2)^(n+1),x],x], x, tmp]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCoth && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*(-Csch[x]^2)^(n+1),x],x], x, tmp] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCoth && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


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
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCoth[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCoth[u])/(d*(m+1)) - 
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1-u^2),x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[v_*(a_.+b_.*ArcTanh[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcTanh[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/(1-u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcTanh[u]),x]]


Int[v_*(a_.+b_.*ArcCoth[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcCoth[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/(1-u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcCoth[u]),x]]


(* ::Subsection::Closed:: *)
(*Inverse Hyperbolic Secant Functions*)


Int[ArcSech[c_.*x_],x_Symbol] :=
  x*ArcSech[c*x] + Sqrt[1+c*x]*Sqrt[1/(1+c*x)]*Int[1/(Sqrt[1-c*x]*Sqrt[1+c*x]),x] /;
FreeQ[c,x]


Int[ArcCsch[c_.*x_],x_Symbol] :=
  x*ArcCsch[c*x] + 1/c*Int[1/(x*Sqrt[1+1/(c^2*x^2)]),x] /;
FreeQ[c,x]


Int[(a_.+b_.*ArcSech[c_.*x_])^n_,x_Symbol] :=
  -1/c*Subst[Int[(a+b*x)^n*Sech[x]*Tanh[x],x],x,ArcSech[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcCsch[c_.*x_])^n_,x_Symbol] :=
  -1/c*Subst[Int[(a+b*x)^n*Csch[x]*Coth[x],x],x,ArcCsch[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcSech[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcCosh[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcCsch[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcSinh[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[x_^m_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  x^(m+1)*(a+b*ArcSech[c*x])/(m+1) + 
  b*Sqrt[1+c*x]/(m+1)*Sqrt[1/(1+c*x)]*Int[x^m/(Sqrt[1-c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,m},x] && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  x^(m+1)*(a+b*ArcCsch[c*x])/(m+1) + 
  b/(c*(m+1))*Int[x^(m-1)/Sqrt[1+1/(c^2*x^2)],x] /;
FreeQ[{a,b,c,m},x] && NonzeroQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcSech[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Sech[x]^(m+1)*Tanh[x],x],x,ArcSech[c*x]] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcCsch[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Csch[x]^(m+1)*Coth[x],x],x,ArcCsch[c*x]] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*ArcSech[c*x])^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[x_^m_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*ArcCsch[c*x])^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[(a+b*ArcSech[c*x]),u,x] + b*Sqrt[1+c*x]*Sqrt[1/(1+c*x)]*Int[SimplifyIntegrand[u/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(d+e*x^2)^p,x]]},  
  Dist[(a+b*ArcCsch[c*x]),u,x] - b*c*x/Sqrt[-c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[-1-c^2*x^2]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcSech[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCsch[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSech[c*x])/(2*e*(p+1)) + 
  b*Sqrt[1+c*x]/(2*e*(p+1))*Sqrt[1/(1+c*x)]*Int[(d+e*x^2)^(p+1)/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCsch[c*x])/(2*e*(p+1)) - 
  b*c*x/(2*e*(p+1)*Sqrt[-c^2*x^2])*Int[(d+e*x^2)^(p+1)/(x*Sqrt[-1-c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[(a+b*ArcSech[c*x]),u,x] + b*Sqrt[1+c*x]*Sqrt[1/(1+c*x)]*Int[SimplifyIntegrand[u/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[x^m*(d+e*x^2)^p,x]]},  
  Dist[(a+b*ArcCsch[c*x]),u,x] - b*c*x/Sqrt[-c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[-1-c^2*x^2]),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegersQ[m,p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegersQ[m,p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && IntegerQ[m] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[e-c^2*d] && IntegerQ[m] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcSech[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcCsch[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[ArcSech[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcSech[a+b*x]/b + 
  Int[Sqrt[(1-a-b*x)/(1+a+b*x)]/(1-a-b*x),x] /;
FreeQ[{a,b},x]


Int[ArcCsch[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcCsch[a+b*x]/b + 
  Int[1/((a+b*x)*Sqrt[1+1/(a+b*x)^2]),x] /;
FreeQ[{a,b},x]


Int[ArcSech[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[x^n*Sech[x]*Tanh[x],x],x,ArcSech[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcCsch[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[x^n*Csch[x]*Coth[x],x],x,ArcCsch[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcSech[a_+b_.*x_]/x_,x_Symbol] :=
  -ArcSech[a+b*x]*Log[1+E^(-2*ArcSech[a+b*x])] + 
  ArcSech[a+b*x]*Log[1-(1-Sqrt[1-a^2])/(E^ArcSech[a+b*x]*a)] + 
  ArcSech[a+b*x]*Log[1-(1+Sqrt[1-a^2])/(E^ArcSech[a+b*x]*a)] + 
  1/2*PolyLog[2,-E^(-2*ArcSech[a+b*x])] - 
  PolyLog[2,(1-Sqrt[1-a^2])/(E^ArcSech[a+b*x]*a)] - 
  PolyLog[2,(1+Sqrt[1-a^2])/(E^ArcSech[a+b*x]*a)] /;
FreeQ[{a,b},x]


Int[ArcCsch[a_+b_.*x_]/x_,x_Symbol] :=
  -ArcCsch[a+b*x]^2 - 
  ArcCsch[a+b*x]*Log[1-E^(-2*ArcCsch[a+b*x])] + 
  ArcCsch[a+b*x]*Log[1+(1-Sqrt[1+a^2])*E^ArcCsch[a+b*x]/a] + 
  ArcCsch[a+b*x]*Log[1+(1+Sqrt[1+a^2])*E^ArcCsch[a+b*x]/a] + 
  1/2*PolyLog[2,E^(-2*ArcCsch[a+b*x])] + 
  PolyLog[2,-(1-Sqrt[1+a^2])*E^ArcCsch[a+b*x]/a] + 
  PolyLog[2,-(1+Sqrt[1+a^2])*E^ArcCsch[a+b*x]/a] /;
FreeQ[{a,b},x]


Int[x_^m_.*ArcSech[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcSech[a+b*x]/(b^(m+1)*(m+1)) + 
  1/(b^(m+1)*(m+1))*Subst[Int[((-a*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[-1+x]*Sqrt[1+x]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NonzeroQ[m+1]


Int[x_^m_.*ArcCsch[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcCsch[a+b*x]/(b^(m+1)*(m+1)) + 
  1/(b^(m+1)*(m+1))*Subst[Int[((-a*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1+x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NonzeroQ[m+1]


Int[x_^m_.*ArcSech[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b^(m+1)*Subst[Int[x^n*(-a+Sech[x])^m*Sech[x]*Tanh[x],x],x,ArcSech[a+b*x]] /;
FreeQ[{a,b,n},x] && PositiveIntegerQ[m]


Int[x_^m_.*ArcCsch[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b^(m+1)*Subst[Int[x^n*(-a+Csch[x])^m*Csch[x]*Coth[x],x],x,ArcCsch[a+b*x]] /;
FreeQ[{a,b,n},x] && PositiveIntegerQ[m]


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
FreeQ[{a,m,p},x] && NonzeroQ[m+1]


Int[x_^m_.*E^ArcCsch[a_.*x_^p_.], x_Symbol] :=
  1/a*Int[x^(m-p),x] + Int[x^m*Sqrt[1+1/(a^2*x^(2*p))],x] /;
FreeQ[{a,m,p},x]


Int[x_^m_.*E^(n_.*ArcSech[u_]), x_Symbol] :=
  Int[x^m*(1/u + Sqrt[(1-u)/(1+u)] + 1/u*Sqrt[(1-u)/(1+u)])^n,x] /;
FreeQ[m,x] && IntegerQ[n]


Int[x_^m_.*E^(n_.*ArcCsch[u_]), x_Symbol] :=
  Int[x^m*(1/u + Sqrt[1+1/u^2])^n,x] /;
FreeQ[m,x] && IntegerQ[n]


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
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCsch[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCsch[u])/(d*(m+1)) - 
  b*u/(d*(m+1)*Sqrt[-u^2])*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[-1-u^2]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSech[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcSech[u]),w,x] + b*Sqrt[1-u^2]/(u*Sqrt[-1+1/u]*Sqrt[1+1/u])*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[1-u^2]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCsch[u_]),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  Dist[(a+b*ArcCsch[u]),w,x] - b*u/Sqrt[-u^2]*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[-1-u^2]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]
