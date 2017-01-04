(* ::Package:: *)

(* ::Section:: *)
(*Logarithm Function Rules*)


(* ::Subsection::Closed:: *)
(*3.1 u (a+b log(c (d (e+f x)^p)^q))^n*)


Int[Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.],x_Symbol] :=
  (e+f*x)*Log[c*(d*(e+f*x)^p)^q]/f - p*q*x /;
FreeQ[{c,d,e,f,p,q},x]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/f - b*n*p*q*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && RationalQ[n] && n>0


Int[1/Log[d_.*(e_.+f_.*x_)],x_Symbol] :=
  LogIntegral[d*(e+f*x)]/(d*f) /;
FreeQ[{d,e,f},x]


Int[1/(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  (e+f*x)/(b*f*p*q*E^(a/(b*p*q))*(c*(d*(e+f*x)^p)^q)^(1/(p*q)))*ExpIntegralEi[(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q)] /;
FreeQ[{a,b,c,d,e,f,p,q},x]


Int[1/Sqrt[a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]],x_Symbol] :=
  Sqrt[Pi]*Rt[b*p*q,2]*(e+f*x)/(b*f*p*q*E^(a/(b*p*q))*(c*(d*(e+f*x)^p)^q)^(1/(p*q)))*
    Erfi[Sqrt[a+b*Log[c*(d*(e+f*x)^p)^q]]/Rt[b*p*q,2]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && PosQ[b*p*q]


Int[1/Sqrt[a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]],x_Symbol] :=
  Sqrt[Pi]*Rt[-b*p*q,2]*(e+f*x)/(b*f*p*q*E^(a/(b*p*q))*(c*(d*(e+f*x)^p)^q)^(1/(p*q)))*
    Erf[Sqrt[a+b*Log[c*(d*(e+f*x)^p)^q]]/Rt[-b*p*q,2]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NegQ[b*p*q]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*f*p*q*(n+1)) - 
  1/(b*p*q*(n+1))*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && RationalQ[n] && n<-1


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/
    (f*E^(a/(b*p*q))*(c*(d*(e+f*x)^p)^q)^(1/(p*q))*(-(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q))^n)*
    Gamma[n+1,-(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q)] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && Not[IntegerQ[2*n]]


Int[1/((g_.+h_.*x_)*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])),x_Symbol] :=
  Log[RemoveContent[a+b*Log[c*(d*(e+f*x)^p)^q],x]]/(b*h*p*q) /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && ZeroQ[f*g-e*h]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  (a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*h*p*q*(n+1)) /;
FreeQ[{a,b,c,d,e,f,g,h,n,p,q},x] && ZeroQ[f*g-e*h] && NonzeroQ[n+1]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/(h*(m+1)) - 
  b*n*p*q/(m+1)*Int[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && ZeroQ[f*g-e*h] && NonzeroQ[m+1] && RationalQ[n] && n>0


Int[(g_.+h_.*x_)^m_./Log[d_.*(e_.+f_.*x_)^p_.],x_Symbol] :=
  (h/f)^(p-1)*LogIntegral[d*(e+f*x)^p]/(d*f*p) /;
FreeQ[{d,e,f,g,h,m,p},x] && ZeroQ[m-(p-1)] && ZeroQ[f*g-e*h] && (IntegerQ[p] || PositiveQ[h/f])


Int[(g_.+h_.*x_)^m_/Log[d_.*(e_.+f_.*x_)^p_.],x_Symbol] :=
  (g+h*x)^(p-1)/(e+f*x)^(p-1)*Int[(e+f*x)^(p-1)/Log[d*(e+f*x)^p],x] /;
FreeQ[{d,e,f,g,h,m,p},x] && ZeroQ[m-(p-1)] && ZeroQ[f*g-e*h] && Not[IntegerQ[p] || PositiveQ[h/f]]


Int[(g_.+h_.*x_)^m_./(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  (g+h*x)^(m+1)/(b*h*p*q*E^(a*(m+1)/(b*p*q))*(c*(d*(e+f*x)^p)^q)^((m+1)/(p*q)))*
    ExpIntegralEi[(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q)] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && ZeroQ[f*g-e*h] && NonzeroQ[m+1]


Int[(g_.+h_.*x_)^m_./Sqrt[a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]],x_Symbol] :=
  Sqrt[Pi]*(g+h*x)^(m+1)/(b*h*p*q*Rt[(m+1)/(b*p*q),2]*E^(a*(m+1)/(b*p*q))*(c*(d*(e+f*x)^p)^q)^((m+1)/(p*q)))*
    Erfi[Rt[(m+1)/(b*p*q),2]*Sqrt[a+b*Log[c*(d*(e+f*x)^p)^q]]] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && ZeroQ[f*g-e*h] && NonzeroQ[m+1] && PosQ[(m+1)/(b*p*q)]


Int[(g_.+h_.*x_)^m_./Sqrt[a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]],x_Symbol] :=
  Sqrt[Pi]*(g+h*x)^(m+1)/(b*h*p*q*Rt[-(m+1)/(b*p*q),2]*E^(a*(m+1)/(b*p*q))*(c*(d*(e+f*x)^p)^q)^((m+1)/(p*q)))*
    Erf[Rt[-(m+1)/(b*p*q),2]*Sqrt[a+b*Log[c*(d*(e+f*x)^p)^q]]] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && ZeroQ[f*g-e*h] && NonzeroQ[m+1] && NegQ[(m+1)/(b*p*q)]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*h*p*q*(n+1)) - 
  (m+1)/(b*p*q*(n+1))*Int[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && ZeroQ[f*g-e*h] && NonzeroQ[m+1] && RationalQ[n] && n<-1


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/
    (h*(m+1)*E^(a*(m+1)/(b*p*q))*(c*(d*(e+f*x)^p)^q)^((m+1)/(p*q))*(-(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q))^n)*
    Gamma[n+1,-(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q)] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && ZeroQ[f*g-e*h] && NonzeroQ[m+1]


Int[Log[c_.*(e_.+f_.*x_)]/(g_.+h_.*x_),x_Symbol] :=
  -1/h*PolyLog[2,-Together[c*f/h]*(g+h*x)] /;
FreeQ[{c,e,f,g,h},x] && ZeroQ[h+c*(f*g-e*h)]


Int[(a_.+b_.*Log[c_.*(e_.+f_.*x_)])/(g_.+h_.*x_),x_Symbol] :=
  (a+b*Log[c*(e-f*g/h)])*Log[g+h*x]/h + b*Int[Log[-h*(e+f*x)/(f*g-e*h)]/(g+h*x),x] /;
FreeQ[{a,b,c,e,f,g,h},x] && NonzeroQ[h+c*(f*g-e*h)] && PositiveQ[c*(e-f*g/h)]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  (a+b*Log[c*(d*(e+f*x)^p)^q])^n/h*Log[f*(g+h*x)/(f*g-e*h)] - 
  b*f*n*p*q/h*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1)*Log[f*(g+h*x)/(f*g-e*h)]/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && NonzeroQ[f*g-e*h] && PositiveIntegerQ[n]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])/(h*(m+1)) - 
  b*f*p*q/(h*(m+1))*Int[(g+h*x)^(m+1)/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && NonzeroQ[f*g-e*h] && NonzeroQ[m+1]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_/(g_.+h_.*x_)^2,x_Symbol] :=
  (e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/((f*g-e*h)*(g+h*x)) - 
  b*f*n*p*q/(f*g-e*h)*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1)/(g+h*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && NonzeroQ[f*g-e*h] && RationalQ[n] && n>0


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/(h*(m+1)) - 
  b*f*n*p*q/(h*(m+1))*Int[(g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1)/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && NonzeroQ[f*g-e*h] && RationalQ[n] && n>0 && NonzeroQ[m+1] && IntegersQ[2*m,2*n] && 
  (n==1 || Not[PositiveIntegerQ[m]] || n==2 && NonzeroQ[m-1])


Int[(g_.+h_.*x_)^m_./(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)^m/(a+b*Log[c*(d*(e+f*x)^p)^q]),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && NonzeroQ[f*g-e*h] && PositiveIntegerQ[m]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (e+f*x)*(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*f*p*q*(n+1)) + 
  m*(f*g-e*h)/(b*f*p*q*(n+1))*Int[(g+h*x)^(m-1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1),x] - 
  (m+1)/(b*p*q*(n+1))*Int[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && NonzeroQ[f*g-e*h] && RationalQ[m,n] && n<-1 && m>0


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p,q},x] && NonzeroQ[f*g-e*h] && PositiveIntegerQ[m]


Int[u_^m_.*(a_.+b_.*Log[c_.*(d_.*v_^p_)^q_.])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Log[c*(d*ExpandToSum[v,x]^p)^q])^n,x] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  Defer[Int][(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x]


Int[Log[c_./(e_.+f_.*x_)]/((g_.+h_.*x_)*(i_.+j_.*x_)),x_Symbol] :=
  f/(h*(f*i-e*j))*PolyLog[2,Simplify[f*(i+j*x)/(j*(e+f*x))]] /;
FreeQ[{c,e,f,g,h,i,j},x] && ZeroQ[f*g-e*h] && ZeroQ[f*i+j*(c-e)]


Int[(a_+b_.*Log[c_./(e_.+f_.*x_)])/((g_.+h_.*x_)*(i_.+j_.*x_)),x_Symbol] :=
  a*Int[1/((g+h*x)*(i+j*x)),x] + b*Int[Log[c/(e+f*x)]/((g+h*x)*(i+j*x)),x] /;
FreeQ[{a,b,c,e,f,g,h,i,j},x] && ZeroQ[f*g-e*h] && ZeroQ[f*i+j*(c-e)]


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(g_.+h_.*x_),x_Symbol] :=
  With[{u=IntHide[(i+j*x)^m/(g+h*x),x]},
  Dist[a+b*Log[c*(d*(e+f*x)^p)^q],u] - b*h*p*q*Int[SimplifyIntegrand[u/(g+h*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q},x] && ZeroQ[f*g-e*h] && IntegerQ[m+1/2]


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(e_.+f_.*x_)])^n_./(g_.+h_.*x_),x_Symbol] :=
  1/(c^m*f^m*h)*Subst[Int[(a+b*x)^n*(c*f*i-c*e*j+j*E^x)^m,x],x,Log[c*(e+f*x)]] /;
FreeQ[{a,b,c,e,f,g,h,i,j,n},x] && ZeroQ[f*g-e*h] && PositiveIntegerQ[m] && (IntegerQ[n] || m>0)


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*(d*(e+f*x)^p)^q])^n,(i+j*x)^m/(g+h*x),x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q},x] && IntegerQ[m] && PositiveIntegerQ[n]


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  Defer[Int][(i+j*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/(g+h*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n,p,q},x]


Int[Log[c_./(e_.+f_.*x_)]/(g_+h_.*x_^2),x_Symbol] :=
  -f/(2*e*h)*PolyLog[2,Simplify[(-e+f*x)/(e+f*x)]] /;
FreeQ[{c,e,f,g,h},x] && ZeroQ[f^2*g+e^2*h] && ZeroQ[c-2*e]


Int[(a_.+b_.*Log[c_./(e_.+f_.*x_)])/(g_+h_.*x_^2),x_Symbol] :=
  (a+b*Log[c/(2*e)])*Int[1/(g+h*x^2),x] + b*Int[Log[2*e/(e+f*x)]/(g+h*x^2),x] /;
FreeQ[{c,e,f,g,h},x] && ZeroQ[f^2*g+e^2*h] && PositiveQ[c/(2*e)] && (NonzeroQ[c-2*e] || NonzeroQ[a])


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(g_.+h_.*x_+i_.*x_^2),x_Symbol] :=
  e*f*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/((e+f*x)*(f*g+e*i*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,p,q},x] && ZeroQ[f^2*g-e*f*h+e^2*i]


Int[(a_.+b_.*Log[c_.*(d_.*(e_+f_.*x_)^p_.)^q_.])/(g_+i_.*x_^2),x_Symbol] :=
  e*f*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/((e+f*x)*(f*g+e*i*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,i,p,q},x] && ZeroQ[f^2*g+e^2*i]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/Sqrt[g_+h_.*x_^2],x_Symbol] :=
  With[{u=IntHide[1/Sqrt[g+h*x^2],x]},  
  u*(a+b*Log[c*(d*(e+f*x)^p)^q]) - b*f*p*q*Int[SimplifyIntegrand[u/(e+f*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && PositiveQ[g]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(Sqrt[g1_+h1_.*x_]*Sqrt[g2_+h2_.*x_]),x_Symbol] :=
  With[{u=IntHide[1/Sqrt[g1*g2+h1*h2*x^2],x]},  
  u*(a+b*Log[c*(d*(e+f*x)^p)^q]) - b*f*p*q*Int[SimplifyIntegrand[u/(e+f*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g1,h1,g2,h2,p,q},x] && ZeroQ[g2*h1+g1*h2] && PositiveQ[g1] && PositiveQ[g2]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/Sqrt[g_+h_.*x_^2],x_Symbol] :=
  Sqrt[1+h/g*x^2]/Sqrt[g+h*x^2]*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/Sqrt[1+h/g*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && Not[PositiveQ[g]]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(Sqrt[g1_+h1_.*x_]*Sqrt[g2_+h2_.*x_]),x_Symbol] :=
  Sqrt[1+h1*h2/(g1*g2)*x^2]/(Sqrt[g1+h1*x]*Sqrt[g2+h2*x])*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/Sqrt[1+h1*h2/(g1*g2)*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g1,h1,g2,h2,p,q},x] && ZeroQ[g2*h1+g1*h2]


Int[Log[i_.*(j_.+k_.*x_)]/(g_.+h_.*x_)*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  -PolyLog[2,Together[1-i*(j+k*x)]]/h*(a+b*Log[c*(d*(e+f*x)^p)^q])^n + 
  b*f*n*p*q/h*Int[PolyLog[2,Together[1-i*(j+k*x)]]/(e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,p,q},x] && RationalQ[n] && n>0 && ZeroQ[h-i*(h*j-g*k)]


Int[Log[1+i_.*(j_.+k_.*x_)^m_.]/(g_.+h_.*x_)*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  -PolyLog[2,-i*(j+k*x)^m]/(h*m)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n + 
  b*f*n*p*q/(h*m)*Int[PolyLog[2,-i*(j+k*x)^m]/(e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,m,p,q},x] && RationalQ[n] && n>0 && ZeroQ[h*j-g*k]


Int[PolyLog[r_,i_.*(j_.+k_.*x_)^m_.]/(g_.+h_.*x_)*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  PolyLog[r+1,i*(j+k*x)^m]/(h*m)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n - 
  b*f*n*p*q/(h*m)*Int[PolyLog[r+1,i*(j+k*x)^m]/(e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,m,p,q,r},x] && RationalQ[n] && n>0 && ZeroQ[h*j-g*k]


Int[Px_.*F_[g_.+h_.*x_]^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  With[{u=IntHide[Px*F[g+h*x]^m,x]},
  Dist[(a+b*Log[c*(d*(e+f*x)^p)^q]),u,x] - b*f*p*q*Int[SimplifyIntegrand[u/(e+f*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && PolynomialQ[Px,x] && PositiveIntegerQ[m] && 
  MemberQ[{Log,ArcSin,ArcCos,ArcTan,ArcCot,ArcSinh, ArcCosh,ArcTanh, ArcCoth},F]


Int[(a_.+b_.*Log[c_.*(d_.*(e_+f_.*x_^m_)^p_.)^q_.])^n_./x_,x_Symbol] :=
  1/m*Subst[Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^n/x,x],x,x^m] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*Log[c_.*(d_.*(x_^m_*(f_+e_.*x_^r_.))^p_.)^q_.])^n_./x_,x_Symbol] :=
  1/m*Subst[Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^n/x,x],x,x^m] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && ZeroQ[m+r] && PositiveIntegerQ[n]


Int[x_^r1_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_^r_)^p_.)^q_.])^n_.,x_Symbol] :=
  1/r*Subst[Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x],x,x^r] /;
FreeQ[{a,b,c,d,e,f,n,p,q,r},x] && ZeroQ[r1-(r-1)]


Int[x_^r1_.*(g_.+h_.*x_^r_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_^r_)^p_.)^q_.])^n_.,x_Symbol] :=
  1/r*Subst[Int[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x],x,x^r] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q,r},x] && ZeroQ[r1-(r-1)]


Int[(a_.+b_.*Log[c_.*x_^n_.])/(d_+e_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(d+e*x^2),x]},  
  Dist[(a+b*Log[c*x^n]),u] - b*n*Int[u/x,x]] /;
FreeQ[{a,b,c,d,e,n},x]


Int[Log[c_.*(a_.+b_.*x_^mn_)]/(x_*(d_+e_.*x_^n_.)),x_Symbol] :=
  1/(d*n)*PolyLog[2,-Together[b*c*(d+e*x^n)/(d*x^n)]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n+mn] && ZeroQ[d-a*c*d+b*c*e]


Int[Log[c_.*x_^mn_*(b_.+a_.*x_^n_.)]/(x_*(d_+e_.*x_^n_.)),x_Symbol] :=
  1/(d*n)*PolyLog[2,-Together[b*c*(d+e*x^n)/(d*x^n)]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n+mn] && ZeroQ[d-a*c*d+b*c*e]


Int[Px_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p,q},x] && PolynomialQ[Px,x]


Int[RFx_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*(d*(e+f*x)^p)^q])^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[RFx_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[RFx*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[u_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_+g_.*x_^2)^p_.)^q_.])^n_.,x_Symbol] :=
  Int[u*(a+b*Log[c*(d*(f+2*g*x)^(2*p)/(4^p*g^p))^q])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,q,n},x] && ZeroQ[f^2-4*e*g] && IntegerQ[p]


Int[u_.*(a_.+b_.*Log[c_.*(d_.*v_^p_.)^q_.])^n_.,x_Symbol] :=
  Int[u*(a+b*Log[c*(d*ExpandToSum[v,x]^p)^q])^n,x] /;
FreeQ[{a,b,c,d,n,p,q},x] && LinearQ[v,x] && 
  Not[MatchQ[c*(d*v^p)^q, cc_.*(dd_.*(e_.+f_.*x)^pp_.)^qq_. /; FreeQ[{cc,dd,e,f,pp,qq},x]]]


Int[Log[a_.*(b_.*(c_.*x_^n_.)^p_)^q_]^r_.,x_Symbol] :=
  Subst[Int[Log[x^(n*p*q)]^r,x],x^(n*p*q),a*(b*(c*x^n)^p)^q] /;
FreeQ[{a,b,c,n,p,q,r},x]


Int[x_^m_.*Log[a_.*(b_.*(c_.*x_^n_.)^p_)^q_]^r_.,x_Symbol] :=
  Subst[Int[x^m*Log[x^(n*p*q)]^r,x],x^(n*p*q),a*(b*(c*x^n)^p)^q] /;
FreeQ[{a,b,c,m,n,p,q,r},x] && NonzeroQ[m+1] && Not[x^(n*p*q)===a*(b*(c*x^n)^p)^q]





(* ::Subsection::Closed:: *)
(*3.2 u log(e ((a+b x) (c+d x)^-1)^n)^p*)


Int[u_.*Log[e_.*(e1_.*(a_.+b_.*x_)/(c_.+d_.*x_))^n_.]^p_.,x_Symbol] :=
  Log[e*(e1*b/d)^n]^p*Int[u,x] /;
FreeQ[{a,b,c,d,e,n,p,e1},x] && ZeroQ[b*c-a*d]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_.,x_Symbol] :=
  (a+b*x)/b*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p - 
  n*n1*p*(b*c-a*d)/b*Int[Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[p]


Int[Log[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]/(f_.+g_.*x_),x_Symbol] :=
  1/g*PolyLog[2,Together[c-a*e]/(c+d*x)] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && ZeroQ[d*f-c*g] && ZeroQ[d-b*e]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./(f_.+g_.*x_),x_Symbol] :=
  -1/g*Log[(b*c-a*d)/(b*(c+d*x))]*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p + 
  n*n1*p*(b*c-a*d)/g*Int[Log[(b*c-a*d)/(b*(c+d*x))]/((a+b*x)*(c+d*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[d*f-c*g] && PositiveIntegerQ[p]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./(f_.+g_.*x_),x_Symbol] :=
  -1/g*Log[-(b*c-a*d)/(d*(a+b*x))]*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p + 
  n*n1*p*(b*c-a*d)/g*Int[Log[-(b*c-a*d)/(d*(a+b*x))]/((a+b*x)*(c+d*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[b*f-a*g] && PositiveIntegerQ[p]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]/(f_.+g_.*x_),x_Symbol] :=
  Log[f+g*x]/g*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n] - 
  n*n1*(b*c-a*d)/g*Int[Log[f+g*x]/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[d*f-c*g]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_/(f_.+g_.*x_),x_Symbol] :=
  d/g*Int[1/(c+d*x)*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] - 
  (d*f-c*g)/g*Int[(1/((c+d*x)*(f+g*x)))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[d*f-c*g] && IntegerQ[p] && p>1


Int[1/((f_.+g_.*x_)^2*Log[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]),x_Symbol] :=
  d^2/((b*c-a*d)*e*g^2)*LogIntegral[e*(a+b*x)/(c+d*x)] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && ZeroQ[d*f-c*g]


Int[1/((f_.+g_.*x_)^2*Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]),x_Symbol] :=
  d^2*(a+b*x)/(g^2*n*n1*(b*c-a*d)*(c+d*x))*ExpIntegralEi[1/(n*n1)*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]]/
    (e*(e1*(a+b*x)^n1*(c+d*x)^n2)^n)^(1/(n*n1)) /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[d*f-c*g]


Int[1/((f_.+g_.*x_)^2*Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]),x_Symbol] :=
  b^2*(c+d*x)/(g^2*n*n1*(b*c-a*d)*(a+b*x))*(e*(e1*(a+b*x)^n1*(c+d*x)^n2)^n)^(1/(n*n1))*
    ExpIntegralEi[-1/(n*n1)*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[b*f-a*g]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./(f_.+g_.*x_)^2,x_Symbol] :=
  (a+b*x)/((b*f-a*g)*(f+g*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p - 
  n*n1*p*(b*c-a*d)/(b*f-a*g)*Int[1/((c+d*x)*(f+g*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[b*f-a*g] && PositiveIntegerQ[p]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./(f_.+g_.*x_)^2,x_Symbol] :=
  (c+d*x)/((d*f-c*g)*(f+g*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p - 
  n*n1*p*(b*c-a*d)/(d*f-c*g)*Int[1/((a+b*x)*(f+g*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[d*f-c*g] && PositiveIntegerQ[p]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_/(f_.+g_.*x_)^3,x_Symbol] :=
  b/(b*f-a*g)*Int[1/(f+g*x)^2*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] - 
  g/(b*f-a*g)*Int[(a+b*x)/(f+g*x)^3*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[b*f-a*g] && ZeroQ[d*f-c*g]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_/(f_.+g_.*x_)^3,x_Symbol] :=
  d/(d*f-c*g)*Int[1/(f+g*x)^2*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] - 
  g/(d*f-c*g)*Int[(c+d*x)/(f+g*x)^3*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[d*f-c*g] && ZeroQ[b*f-a*g]


Int[(f_.+g_.*x_)^m_.*Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_.,x_Symbol] :=
  (f+g*x)^(m+1)/(g*(m+1))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p - 
  n*n1*p*(b*c-a*d)/(g*(m+1))*Int[(f+g*x)^(m+1)/((a+b*x)*(c+d*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[p] && IntegerQ[m] && NonzeroQ[m+1]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^m2_.*Log[e_.*u_^n_]^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*Log[e*u^n]^p/((m+1)*(b*c-a*d)*(c+d*x)^(m+1)) - 
  n*p/(m+1)*Int[(a+b*x)^m/(c+d*x)^(m+2)*Log[e*u^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,n,Simplify[u*(c+d*x)/(a+b*x)]},x] && ZeroQ[m2+m+2] && NonzeroQ[b*c-a*d] && NonzeroQ[m+1] && RationalQ[p] && p>0


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^m2_.*Log[u_]^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*Log[u]^p/((m+1)*(b*c-a*d)*(c+d*x)^(m+1)) - 
  p/(m+1)*Int[(a+b*x)^m/(c+d*x)^(m+2)*Log[u]^(p-1),x] /;
FreeQ[{a,b,c,d,Simplify[u*(c+d*x)/(a+b*x)]},x] && ZeroQ[m2+m+2] && NonzeroQ[b*c-a*d] && NonzeroQ[m+1] && RationalQ[p] && p>0


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^m2_./Log[e_.*u_^n_],x_Symbol] :=
  (a+b*x)^(m+1)/(n*(b*c-a*d)*(c+d*x)^(m+1))*ExpIntegralEi[(m+1)/n*Log[e*u^n]]/(e*u^n)^((m+1)/n) /;
FreeQ[{a,b,c,d,e,n,Simplify[u*(c+d*x)/(a+b*x)]},x] && ZeroQ[m2+m+2] && NonzeroQ[b*c-a*d] && NonzeroQ[m+1]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^m2_./Log[u_],x_Symbol] :=
  (a+b*x)^(m+1)/((b*c-a*d)*(c+d*x)^(m+1))*ExpIntegralEi[(m+1)*Log[u]]/u^(m+1) /;
FreeQ[{a,b,c,d,Simplify[u*(c+d*x)/(a+b*x)]},x] && ZeroQ[m2+m+2] && NonzeroQ[b*c-a*d] && NonzeroQ[m+1]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^m2_.*Log[e_.*u_^n_]^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*Log[e*u^n]^(p+1)/(n*(p+1)*(b*c-a*d)*(c+d*x)^(m+1)) - 
  (m+1)/(n*(p+1))*Int[(a+b*x)^m/(c+d*x)^(m+2)*Log[e*u^n]^(p+1),x] /;
FreeQ[{a,b,c,d,e,n,Simplify[u*(c+d*x)/(a+b*x)]},x] && ZeroQ[m2+m+2] && NonzeroQ[b*c-a*d] && NonzeroQ[m+1] && RationalQ[p] && p<-1


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^m2_.*Log[u_]^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*Log[u]^(p+1)/((p+1)*(b*c-a*d)*(c+d*x)^(m+1)) - 
  (m+1)/(p+1)*Int[(a+b*x)^m/(c+d*x)^(m+2)*Log[u]^(p+1),x] /;
FreeQ[{a,b,c,d,Simplify[u*(c+d*x)/(a+b*x)]},x] && ZeroQ[m2+m+2] && NonzeroQ[b*c-a*d] && NonzeroQ[m+1] && RationalQ[p] && p<-1


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  d/g*Int[1/(c+d*x)^2*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[b*f-a*g] && ZeroQ[d*f-c*g]


Int[Log[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]/((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  1/(d*f-c*g)*PolyLog[2,Simplify[(c-a*e)*(f+g*x)/(f*(c+d*x))]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*f-a*g] && NonzeroQ[d*f-c*g] && ZeroQ[d*f-c*g-e*(b*f-a*g)]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  -1/(d*f-c*g)*Log[(b*c-a*d)*(f+g*x)/((b*f-a*g)*(c+d*x))]*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p + 
  n*n1*p*(b*c-a*d)/(d*f-c*g)*
    Int[(1/((a+b*x)*(c+d*x)))*Log[(b*c-a*d)*(f+g*x)/((b*f-a*g)*(c+d*x))]*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[b*f-a*g] && NonzeroQ[d*f-c*g] && 
  PositiveIntegerQ[p]


Int[Log[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]/(f_+g_.*x_^2),x_Symbol] :=
  c/(2*d*f)*PolyLog[2,Simplify[(c-a*e)*(c-d*x)/(c*(c+d*x))]] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[d^2*f+c^2*g] && ZeroQ[2*c*d-b*c*e-a*d*e]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./(f_.+g_.*x_+h_.*x_^2),x_Symbol] :=
  d^2*Int[1/((c+d*x)*(d*g-c*h+d*h*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[d^2*f-c*d*g+c^2*h]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./(f_.+h_.*x_^2),x_Symbol] :=
  -d^2/h*Int[1/((c+d*x)*(c-d*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,h,n,p,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[d^2*f+c^2*h]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  b/(g*n*n1*(b*c-a*d))*Subst[Int[x^p,x],x,Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]] /;
FreeQ[{a,b,c,d,e,f,g,n,p,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[d*f-c*g] && ZeroQ[b*f-a*g]


Int[Log[e_.*u_^n_]^p_.*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  -PolyLog[2,Together[1-v]]/(b*c-a*d)*Log[e*u^n]^p + 
  n*p*Int[PolyLog[2,Together[1-v]]/((a+b*x)*(c+d*x))*Log[e*u^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,n,Simplify[u/(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>0


Int[Log[u_]^p_.*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  -PolyLog[2,Together[1-v]]/(b*c-a*d)*Log[u]^p + 
  p*Int[PolyLog[2,Together[1-v]]/((a+b*x)*(c+d*x))*Log[u]^(p-1),x] /;
FreeQ[{a,b,c,d,Simplify[u/(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>0


Int[Log[e_.*u_^n_]^p_*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  With[{f=Simplify[(1-v)/u]},
  Log[v]/(n*(p+1)*(b*c-a*d))*Log[e*u^n]^(p+1) + 
  f/(n*(p+1))*Int[1/((c+d*x)*(c-a*f+(d-b*f)))*Log[e*u^n]^(p+1),x]] /;
FreeQ[{a,b,c,d,e,n,Simplify[u/(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[u_]^p_*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  With[{f=Simplify[(1-v)/u]},
  Log[v]/((p+1)*(b*c-a*d))*Log[u]^(p+1) + 
  f/(p+1)*Int[1/((c+d*x)*(c-a*f+(d-b*f)))*Log[u]^(p+1),x]] /;
FreeQ[{a,b,c,d,Simplify[u/(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[e_.*u_^n_]^p_.*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  PolyLog[2,Together[1-v]]/(b*c-a*d)*Log[e*u^n]^p - 
  n*p*Int[PolyLog[2,Together[1-v]]/((a+b*x)*(c+d*x))*Log[e*u^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,n,Simplify[u*(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>0


Int[Log[u_]^p_.*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  PolyLog[2,Together[1-v]]/(b*c-a*d)*Log[u]^p - 
  p*Int[PolyLog[2,Together[1-v]]/((a+b*x)*(c+d*x))*Log[u]^(p-1),x] /;
FreeQ[{a,b,c,d,Simplify[u*(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>0


Int[Log[e_.*u_^n_]^p_*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  With[{f=Simplify[u*(1-v)]},
  Log[v]/(n*(p+1)*(b*c-a*d))*Log[e*u^n]^(p+1) - 
  f/(n*(p+1))*Int[1/((a+b*x)*(a-c*f+(b-d*f)))*Log[e*u^n]^(p+1),x]] /;
FreeQ[{a,b,c,d,e,n,Simplify[u*(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[u_]^p_*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  With[{f=Simplify[u*(1-v)]},
  Log[v]/((p+1)*(b*c-a*d))*Log[u]^(p+1) - 
  f/(p+1)*Int[1/((a+b*x)*(a-c*f+(b-d*f)))*Log[u]^(p+1),x]] /;
FreeQ[{a,b,c,d,Simplify[u*(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[e_.*u_^n_]^p_*PolyLog[q_,v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  PolyLog[q+1,v]/(b*c-a*d)*Log[e*u^n]^p - 
  n*p*Int[PolyLog[q+1,v]/((a+b*x)*(c+d*x))*Log[e*u^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,n,q,Simplify[u/v],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>1


Int[Log[u_]^p_*PolyLog[q_,v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  PolyLog[q+1,v]/(b*c-a*d)*Log[u]^p - 
  p*Int[PolyLog[q+1,v]/((a+b*x)*(c+d*x))*Log[u]^(p-1),x] /;
FreeQ[{a,b,c,d,q,Simplify[u/v],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>1


Int[Log[e_.*u_^n_]^p_*PolyLog[q_,v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  PolyLog[q,v]/(n*(p+1)*(b*c-a*d))*Log[e*u^n]^(p+1) - 
  1/(n*(p+1))*Int[PolyLog[q-1,v]/((a+b*x)*(c+d*x))*Log[e*u^n]^(p+1),x] /;
FreeQ[{a,b,c,d,e,n,q,Simplify[u/v],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[u_]^p_*PolyLog[q_,v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  PolyLog[q,v]/((p+1)*(b*c-a*d))*Log[u]^(p+1) - 
  1/(p+1)*Int[PolyLog[q-1,v]/((a+b*x)*(c+d*x))*Log[u]^(p+1),x] /;
FreeQ[{a,b,c,d,q,Simplify[u/v],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[e_.*u_^n_]^p_*PolyLog[q_,v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  -PolyLog[q+1,v]/(b*c-a*d)*Log[e*u^n]^p + 
  n*p*Int[PolyLog[q+1,v]/((a+b*x)*(c+d*x))*Log[e*u^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,n,q,Simplify[u*v],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>1


Int[Log[u_]^p_*PolyLog[q_,v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  -PolyLog[q+1,v]/(b*c-a*d)*Log[u]^p + 
  p*Int[PolyLog[q+1,v]/((a+b*x)*(c+d*x))*Log[u]^(p-1),x] /;
FreeQ[{a,b,c,d,q,Simplify[u*v],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>1


Int[Log[e_.*u_^n_]^p_*PolyLog[q_,v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  PolyLog[q,v]/(n*(p+1)*(b*c-a*d))*Log[e*u^n]^(p+1) + 
  1/(n*(p+1))*Int[PolyLog[q-1,v]/((a+b*x)*(c+d*x))*Log[e*u^n]^(p+1),x] /;
FreeQ[{a,b,c,d,e,n,q,Simplify[u*v],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[u_]^p_*PolyLog[q_,v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  PolyLog[q,v]/((p+1)*(b*c-a*d))*Log[u]^(p+1) + 
  1/(p+1)*Int[PolyLog[q-1,v]/((a+b*x)*(c+d*x))*Log[u]^(p+1),x] /;
FreeQ[{a,b,c,d,q,Simplify[u*v],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[u_./(f_.+g_.*x_+h_.*x_^2)*Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_.,x_Symbol] :=
  b*d/h*Int[u/((a+b*x)*(c+d*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[b*d*f-a*c*h] && ZeroQ[b*d*g-b*c*h-a*d*h]


Int[u_./(f_.+h_.*x_^2)*Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_.,x_Symbol] :=
  b*d/h*Int[u/((a+b*x)*(c+d*x))*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,h,n,p,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[b*d*f-a*c*h] && ZeroQ[b*c+a*d]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]/(f_+g_.*x_+h_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(f+g*x+h*x^2),x]},  
  u*Log[e*(e1*(a+b*x)^n1*(c+d*x)^n2)^n] - n*(b*c-a*d)*Int[u/((a+b*x)*(c+d*x)),x]] /;
FreeQ[{a,b,c,d,e,e1,f,g,h,n,n1},x] && ZeroQ[n1+n2]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]/(f_+h_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(f+h*x^2),x]},  
  u*Log[e*(e1*(a+b*x)^n1*(c+d*x)^n2)^n] - n*(b*c-a*d)*Int[u/((a+b*x)*(c+d*x)),x]] /;
FreeQ[{a,b,c,d,e,e1,f,h,n,n1},x] && ZeroQ[n1+n2]


Int[RFx_*Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Log[e*(e1*(a+b*x)^n1*(c+d*x)^n2)^n]^p,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n,e1,n1},x] && ZeroQ[n1+n2] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[p]


Int[u_.*Log[v_]^p_.,x_Symbol] :=
  With[{lst=QuotientOfLinearsParts[v,x]},
  Int[u*Log[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^p,x] /;
 Not[OneQ[p] && ZeroQ[lst[[3]]]]] /;
FreeQ[p,x] && QuotientOfLinearsQ[v,x] && Not[QuotientOfLinearsMatchQ[v,x]]





(* ::Subsection::Closed:: *)
(*3.3 Miscellaneous logarithms*)


Int[Log[c_.*(a_.+b_.*x_^n_)^p_.],x_Symbol] :=
  x*Log[c*(a+b*x^n)^p] -
  b*n*p*Int[x^n/(a+b*x^n),x] /;
FreeQ[{a,b,c,n,p},x]


Int[Log[c_.*v_^p_.],x_Symbol] :=
  Int[Log[c*ExpandToSum[v,x]^p],x] /;
FreeQ[{c,p},x] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_^n_)^p_.])/(f_.+g_.*x_),x_Symbol] :=
  Log[f+g*x]*(a+b*Log[c*(d+e*x^n)^p])/g - 
  b*e*n*p/g*Int[x^(n-1)*Log[f+g*x]/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_^n_)^p_.]),x_Symbol] :=
  (f+g*x)^(m+1)*(a+b*Log[c*(d+e*x^n)^p])/(g*(m+1)) - 
  b*e*n*p/(g*(m+1))*Int[x^(n-1)*(f+g*x)^(m+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NonzeroQ[m+1]


Int[u_^m_.*(a_.+b_.*Log[c_.*v_^p_.]),x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Log[c*ExpandToSum[v,x]^p]),x] /;
FreeQ[{a,b,c,m,p},x] && LinearQ[u,x] && BinomialQ[v,x] && Not[LinearMatchQ[u,x] && BinomialMatchQ[v,x]]


Int[ArcSin[f_.+g_.*x_]^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_^n_)^p_.]),x_Symbol] :=
  With[{w=IntHide[ArcSin[f+g*x]^m,x]},  
  Dist[a+b*Log[c*(d+e*x^n)^p],w,x] - 
  b*e*n*p*Int[SimplifyIntegrand[x^(n-1)*w/(d+e*x^n),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && PositiveIntegerQ[m]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_^2)^p_.])/(f_.+g_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(f+g*x^2),x]},  
  u*(a+b*Log[c*(d+e*x^2)^p]) - 2*b*e*p*Int[(x*u)/(d+e*x^2),x]] /;
FreeQ[{a,b,c,d,e,f,g,p},x]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^2)^p_.])^n_,x_Symbol] :=
  x*(a+b*Log[c*(d+e*x^2)^p])^n - 
  2*b*e*n*p*Int[x^2*(a+b*Log[c*(d+e*x^2)^p])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && PositiveIntegerQ[n]


Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^2)^p_.])^n_,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*(a+b*Log[c*(d+e*x)^p])^n,x],x,x^2] /;
FreeQ[{a,b,c,d,e,p},x] && PositiveIntegerQ[n] && IntegerQ[(m-1)/2]


Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^2)^p_.])^n_,x_Symbol] :=
  x^(m+1)*(a+b*Log[c*(d+e*x^2)^p])^n/(m+1) - 
  2*b*e*n*p/(m+1)*Int[x^(m+2)*(a+b*Log[c*(d+e*x^2)^p])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && PositiveIntegerQ[n] && Not[IntegerQ[(m-1)/2]]


Int[u_*Log[v_],x_Symbol] :=
  With[{w=DerivativeDivides[v,u*(1-v),x]},
  w*PolyLog[2,Together[1-v]] /;
 Not[FalseQ[w]]]


Int[(a_.+b_.*Log[u_])*Log[v_]*w_,x_Symbol] :=
  With[{z=DerivativeDivides[v,w*(1-v),x]},
  z*(a+b*Log[u])*PolyLog[2,Together[1-v]] - 
  b*Int[SimplifyIntegrand[z*PolyLog[2,Together[1-v]]*D[u,x]/u,x],x] /;
 Not[FalseQ[z]]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x]


Int[Log[c_.*(a_+b_.*(d_.+e_.*x_)^n_)^p_.],x_Symbol] :=
  (d+e*x)*Log[c*(a+b*(d+e*x)^n)^p]/e -
  b*n*p*Int[1/(b+a*(d+e*x)^(-n)),x] /;
FreeQ[{a,b,c,d,e,p},x] && RationalQ[n] && n<0


Int[Log[c_.*(a_+b_.*(d_.+e_.*x_)^n_.)^p_.],x_Symbol] :=
  (d+e*x)*Log[c*(a+b*(d+e*x)^n)^p]/e - n*p*x +
  a*n*p*Int[1/(a+b*(d+e*x)^n),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[RationalQ[n] && n<0]


Int[(a_.+b_.*Log[c_.*(d_+e_./(f_.+g_.*x_))^p_.])^n_.,x_Symbol] :=
  (e+d*(f+g*x))*(a+b*Log[c*(d+e/(f+g*x))^p])^n/(d*g) - 
  b*e*n*p/(d*g)*Subst[Int[(a+b*Log[c*(d+e*x)^p])^(n-1)/x,x],x,1/(f+g*x)] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  x*(a+b*Log[c*RFx^p])^n - 
  b*n*p*Int[SimplifyIntegrand[x*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x],x] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[(a_.+b_.*Log[c_.*RFx_^p_.])^n_./(d_.+e_.*x_),x_Symbol] :=
  Log[d+e*x]*(a+b*Log[c*RFx^p])^n/e - 
  b*n*p/e*Int[Log[d+e*x]*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x] /;
FreeQ[{a,b,c,d,e,p},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*Log[c*RFx^p])^n/(e*(m+1)) - 
  b*n*p/(e*(m+1))*Int[SimplifyIntegrand[(d+e*x)^(m+1)*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x],x] /;
FreeQ[{a,b,c,d,e,m,p},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n] && (n==1 || IntegerQ[m]) && NonzeroQ[m+1]


Int[Log[c_.*RFx_^n_.]/(d_+e_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(d+e*x^2),x]},  
  u*Log[c*RFx^n] - n*Int[SimplifyIntegrand[u*D[RFx,x]/RFx,x],x]] /;
FreeQ[{c,d,e,n},x] && RationalFunctionQ[RFx,x] && Not[PolynomialQ[RFx,x]]


Int[Log[c_.*Px_^n_.]/Qx_,x_Symbol] :=
  With[{u=IntHide[1/Qx,x]},  
  u*Log[c*Px^n] - n*Int[SimplifyIntegrand[u*D[Px,x]/Px,x],x]] /;
FreeQ[{c,n},x] && QuadraticQ[{Qx,Px},x] && ZeroQ[D[Px/Qx,x]]


Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*RFx^p])^n,RGx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && PositiveIntegerQ[n]


Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[RGx*(a+b*Log[c*RFx^p])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && PositiveIntegerQ[n]


Int[RFx_*(a_.+b_.*Log[u_]),x_Symbol] :=
  With[{lst=SubstForFractionalPowerOfLinear[RFx*(a+b*Log[u]),x]},
  lst[[2]]*lst[[4]]*Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])] /;
 Not[FalseQ[lst]]] /;
FreeQ[{a,b},x] && RationalFunctionQ[RFx,x]


Int[(f_.+g_.*x_)^m_.*Log[1+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  -(f+g*x)^m*PolyLog[2,-e*(F^(c*(a+b*x)))^n]/(b*c*n*Log[F]) + 
  g*m/(b*c*n*Log[F])*Int[(f+g*x)^(m-1)*PolyLog[2,-e*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,e,f,g,n},x] && RationalQ[m] && m>0


Int[(f_.+g_.*x_)^m_.*Log[d_+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  (f+g*x)^(m+1)*Log[d+e*(F^(c*(a+b*x)))^n]/(g*(m+1)) - 
  (f+g*x)^(m+1)*Log[1+e/d*(F^(c*(a+b*x)))^n]/(g*(m+1)) + 
  Int[(f+g*x)^m*Log[1+e/d*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && RationalQ[m] && m>0 && NonzeroQ[d-1]


Int[Log[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  x*Log[d+e*x+f*Sqrt[a+b*x+c*x^2]] + 
  f^2*(b^2-4*a*c)/2*Int[x/((2*d*e-b*f^2)*(a+b*x+c*x^2)-f*(b*d-2*a*e+(2*c*d-b*e)*x)*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[e^2-c*f^2]


Int[Log[d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]],x_Symbol] :=
  x*Log[d+e*x+f*Sqrt[a+c*x^2]] - 
  a*c*f^2*Int[x/(d*e*(a+c*x^2)+f*(a*e-c*d*x)*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[e^2-c*f^2]


Int[(g_.*x_)^m_.*Log[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  (g*x)^(m+1)*Log[d+e*x+f*Sqrt[a+b*x+c*x^2]]/(g*(m+1)) + 
  f^2*(b^2-4*a*c)/(2*g*(m+1))*Int[(g*x)^(m+1)/((2*d*e-b*f^2)*(a+b*x+c*x^2)-f*(b*d-2*a*e+(2*c*d-b*e)*x)*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && ZeroQ[e^2-c*f^2] && NonzeroQ[m+1] && IntegerQ[2*m]


Int[(g_.*x_)^m_.*Log[d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]],x_Symbol] :=
  (g*x)^(m+1)*Log[d+e*x+f*Sqrt[a+c*x^2]]/(g*(m+1)) - 
  a*c*f^2/(g*(m+1))*Int[(g*x)^(m+1)/(d*e*(a+c*x^2)+f*(a*e-c*d*x)*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f,g,m},x] && ZeroQ[e^2-c*f^2] && NonzeroQ[m+1] && IntegerQ[2*m]


Int[v_.*Log[d_.+e_.*x_+f_.*Sqrt[u_]],x_Symbol] :=
  Int[v*Log[d+e*x+f*Sqrt[ExpandToSum[u,x]]],x] /;
FreeQ[{d,e,f},x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]] && (ZeroQ[v-1] || MatchQ[v,(g_.*x)^m_. /; FreeQ[{g,m},x]])


Int[Log[u_],x_Symbol] :=
  x*Log[u] - Int[SimplifyIntegrand[x*D[u,x]/u,x],x] /;
InverseFunctionFreeQ[u,x]


Int[Log[u_]/(a_.+b_.*x_),x_Symbol] :=
  Log[a+b*x]*Log[u]/b -
  1/b*Int[SimplifyIntegrand[Log[a+b*x]*D[u,x]/u,x],x] /;
FreeQ[{a,b},x] && RationalFunctionQ[D[u,x]/u,x] && (NonzeroQ[a] || Not[BinomialQ[u,x] && ZeroQ[BinomialDegree[u,x]^2-1]])


Int[(a_.+b_.*x_)^m_.*Log[u_],x_Symbol] :=
  (a+b*x)^(m+1)*Log[u]/(b*(m+1)) - 
  1/(b*(m+1))*Int[SimplifyIntegrand[(a+b*x)^(m+1)*D[u,x]/u,x],x] /;
FreeQ[{a,b,m},x] && InverseFunctionFreeQ[u,x] && NonzeroQ[m+1] (* && Not[FunctionOfQ[x^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]] *)


Int[Log[u_]/Qx_,x_Symbol] :=
  With[{v=IntHide[1/Qx,x]},  
  v*Log[u] - Int[SimplifyIntegrand[v*D[u,x]/u,x],x]] /;
QuadraticQ[Qx,x] && InverseFunctionFreeQ[u,x]


(* Int[x_^m_.*Px_.*Log[u_],x_Symbol] :=
  With[{v=IntHide[x^m*Px,x]},  
  Dist[Log[u],v] - Int[SimplifyIntegrand[v*D[u,x]/u,x],x]] /;
FreeQ[m,x] && PolynomialQ[Px,x] && InverseFunctionFreeQ[u,x] *)


Int[u_^(a_.*x_)*Log[u_],x_Symbol] :=
  u^(a*x)/a - Int[SimplifyIntegrand[x*u^(a*x-1)*D[u,x],x],x] /;
FreeQ[a,x] && InverseFunctionFreeQ[u,x]


Int[v_*Log[u_],x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[Log[u],w,x] - 
  Int[SimplifyIntegrand[w*D[u,x]/u,x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x]


Int[Log[v_]*Log[w_],x_Symbol] :=
  x*Log[v]*Log[w] - 
  Int[SimplifyIntegrand[x*Log[w]*D[v,x]/v,x],x] - 
  Int[SimplifyIntegrand[x*Log[v]*D[w,x]/w,x],x] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*Log[v_]*Log[w_],x_Symbol] :=
  With[{z=IntHide[u,x]},  
  Dist[Log[v]*Log[w],z,x] - 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/v,x],x] - 
  Int[SimplifyIntegrand[z*Log[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[Log[a_.*Log[b_.*x_^n_.]^p_.],x_Symbol] :=
  x*Log[a*Log[b*x^n]^p] - 
  n*p*Int[1/Log[b*x^n],x] /;
FreeQ[{a,b,n,p},x]


Int[Log[a_.*Log[b_.*x_^n_.]^p_.]/x_,x_Symbol] :=
  Log[b*x^n]*(-p+Log[a*Log[b*x^n]^p])/n /;
FreeQ[{a,b,n,p},x]


Int[x_^m_.*Log[a_.*Log[b_.*x_^n_.]^p_.],x_Symbol] :=
  x^(m+1)*Log[a*Log[b*x^n]^p]/(m+1) - 
  n*p/(m+1)*Int[x^m/Log[b*x^n],x] /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1]


Int[(A_.+B_.*Log[c_.+d_.*x_])/Sqrt[a_+b_.*Log[c_.+d_.*x_]],x_Symbol] :=
  (b*A-a*B)/b*Int[1/Sqrt[a+b*Log[c+d*x]],x] +
  B/b*Int[Sqrt[a+b*Log[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[b*A-a*B]


Int[f_^(a_.*Log[u_]),x_Symbol] :=
  Int[u^(a*Log[f]),x] /;
FreeQ[{a,f},x]


(* If[ShowSteps,

Int[u_/x_,x_Symbol] :=
  With[{lst=FunctionOfLog[u,x]},
  ShowStep["","Int[F[Log[a*x^n]]/x,x]","Subst[Int[F[x],x],x,Log[a*x^n]]/n",Hold[
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]] /;
 Not[FalseQ[lst]]] /;
SimplifyFlag && NonsumQ[u],

Int[u_/x_,x_Symbol] :=
  With[{lst=FunctionOfLog[u,x]},
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
 Not[FalseQ[lst]]] /;
NonsumQ[u]] *)


If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{lst=FunctionOfLog[Cancel[x*u],x]},
  ShowStep["","Int[F[Log[a*x^n]]/x,x]","Subst[Int[F[x],x],x,Log[a*x^n]]/n",Hold[
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]] /;
 Not[FalseQ[lst]]] /;
SimplifyFlag && NonsumQ[u],

Int[u_,x_Symbol] :=
  With[{lst=FunctionOfLog[Cancel[x*u],x]},
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
 Not[FalseQ[lst]]] /;
NonsumQ[u]]


Int[u_.*Log[Gamma[v_]],x_Symbol] :=
  (Log[Gamma[v]]-LogGamma[v])*Int[u,x] + Int[u*LogGamma[v],x]


Int[u_.*(a_. w_+b_. w_*Log[v_]^n_.)^p_.,x_Symbol] :=
  Int[u*w^p*(a+b*Log[v]^n)^p,x] /;
FreeQ[{a,b,n},x] && IntegerQ[p]


Int[u_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  Defer[Int][u*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x] /;
FreeQ[{a,b,c,d,e,f,n,p,q},x] && AlgebraicFunctionQ[u,x]



