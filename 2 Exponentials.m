(* ::Package:: *)

(* ::Section:: *)
(*2 Exponentials integration rules*)


(* ::Subsection::Closed:: *)
(*2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p*)


$UseGamma=False;


Int[(c_.+d_.*x_)^m_.*(b_.*F_^(g_.*(e_.+f_.*x_)))^n_.,x_Symbol] :=
  (c+d*x)^m*(b*F^(g*(e+f*x)))^n/(f*g*n*Log[F]) - 
  d*m/(f*g*n*Log[F])*Int[(c+d*x)^(m-1)*(b*F^(g*(e+f*x)))^n,x] /;
FreeQ[{F,b,c,d,e,f,g,n},x] && GtQ[m,0] && IntegerQ[2*m] && Not[$UseGamma===True]


Int[(c_.+d_.*x_)^m_*(b_.*F_^(g_.*(e_.+f_.*x_)))^n_.,x_Symbol] :=
  (c+d*x)^(m+1)*(b*F^(g*(e+f*x)))^n/(d*(m+1)) - 
  f*g*n*Log[F]/(d*(m+1))*Int[(c+d*x)^(m+1)*(b*F^(g*(e+f*x)))^n,x] /;
FreeQ[{F,b,c,d,e,f,g,n},x] && LtQ[m,-1] && IntegerQ[2*m] && Not[$UseGamma===True]


Int[F_^(g_.*(e_.+f_.*x_))/(c_.+d_.*x_),x_Symbol] :=
  F^(g*(e-c*f/d))/d*ExpIntegralEi[f*g*(c+d*x)*Log[F]/d] /;
FreeQ[{F,c,d,e,f,g},x] && Not[$UseGamma===True]


Int[(c_.+d_.*x_)^m_.*F_^(g_.*(e_.+f_.*x_)),x_Symbol] :=
  (-d)^m*F^(g*(e-c*f/d))/(f^(m+1)*g^(m+1)*Log[F]^(m+1))*Gamma[m+1,-f*g*Log[F]/d*(c+d*x)] /;
FreeQ[{F,c,d,e,f,g},x] && IntegerQ[m]


Int[F_^(g_.*(e_.+f_.*x_))/Sqrt[c_.+d_.*x_],x_Symbol] :=
  2/d*Subst[Int[F^(g*(e-c*f/d)+f*g*x^2/d),x],x,Sqrt[c+d*x]] /;
FreeQ[{F,c,d,e,f,g},x] && Not[$UseGamma===True]


Int[(c_.+d_.*x_)^m_*F_^(g_.*(e_.+f_.*x_)),x_Symbol] :=
  -F^(g*(e-c*f/d))*(c+d*x)^FracPart[m]/(d*(-f*g*Log[F]/d)^(IntPart[m]+1)*(-f*g*Log[F]*(c+d*x)/d)^FracPart[m])*
    Gamma[m+1,(-f*g*Log[F]/d)*(c+d*x)] /;
FreeQ[{F,c,d,e,f,g,m},x] && Not[IntegerQ[m]]


Int[(c_.+d_.*x_)^m_.*(b_.*F_^(g_.*(e_.+f_.*x_)))^n_,x_Symbol] :=
  (b*F^(g*(e+f*x)))^n/F^(g*n*(e+f*x))*Int[(c+d*x)^m*F^(g*n*(e+f*x)),x] /;
FreeQ[{F,b,c,d,e,f,g,m,n},x]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*(F^(g*(e+f*x)))^n)^p,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g,m,n},x] && IGtQ[p,0]


Int[(c_.+d_.*x_)^m_./(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.),x_Symbol] :=
  (c+d*x)^(m+1)/(a*d*(m+1)) - b/a*Int[(c+d*x)^m*(F^(g*(e+f*x)))^n/(a+b*(F^(g*(e+f*x)))^n),x] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && IGtQ[m,0]


(* Int[(c_.+d_.*x_)^m_./(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.),x_Symbol] :=
  -(c+d*x)^m/(a*f*g*n*Log[F])*Log[1+a/(b*(F^(g*(e+f*x)))^n)] + 
  d*m/(a*f*g*n*Log[F])*Int[(c+d*x)^(m-1)*Log[1+a/(b*(F^(g*(e+f*x)))^n)],x] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && IGtQ[m,0] *)


Int[(c_.+d_.*x_)^m_.*(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_,x_Symbol] :=
  1/a*Int[(c+d*x)^m*(a+b*(F^(g*(e+f*x)))^n)^(p+1),x] - 
  b/a*Int[(c+d*x)^m*(F^(g*(e+f*x)))^n*(a+b*(F^(g*(e+f*x)))^n)^p,x] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && ILtQ[p,0] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_,x_Symbol] :=
  With[{u=IntHide[(a+b*(F^(g*(e+f*x)))^n)^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && IGtQ[m,0] && LtQ[p,-1]


Int[u_^m_.*(a_.+b_.*(F_^(g_.*v_))^n_.)^p_.,x_Symbol] :=
  Int[NormalizePowerOfLinear[u,x]^m*(a+b*(F^(g*ExpandToSum[v,x]))^n)^p,x] /;
FreeQ[{F,a,b,g,n,p},x] && LinearQ[v,x] && PowerOfLinearQ[u,x] && Not[LinearMatchQ[v,x] && PowerOfLinearMatchQ[u,x]] && IntegerQ[m]


Int[u_^m_.*(a_.+b_.*(F_^(g_.*v_))^n_.)^p_.,x_Symbol] :=
  Module[{uu=NormalizePowerOfLinear[u,x],z},
  z=If[PowerQ[uu] && FreeQ[uu[[2]],x], uu[[1]]^(m*uu[[2]]), uu^m];
  uu^m/z*Int[z*(a+b*(F^(g*ExpandToSum[v,x]))^n)^p,x]] /; 
FreeQ[{F,a,b,g,m,n,p},x] && LinearQ[v,x] && PowerOfLinearQ[u,x] && Not[LinearMatchQ[v,x] && PowerOfLinearMatchQ[u,x]] && 
  Not[IntegerQ[m]]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
  Unintegrable[(c+d*x)^m*(a+b*(F^(g*(e+f*x)))^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]





(* ::Subsection::Closed:: *)
(*2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p*)


Int[(c_.+d_.*x_)^m_.*(F_^(g_.*(e_.+f_.*x_)))^n_./(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.),x_Symbol] :=
  (c+d*x)^m/(b*f*g*n*Log[F])*Log[1+b*(F^(g*(e+f*x)))^n/a] - 
  d*m/(b*f*g*n*Log[F])*Int[(c+d*x)^(m-1)*Log[1+b*(F^(g*(e+f*x)))^n/a],x] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && IGtQ[m,0]


Int[(c_.+d_.*x_)^m_.*(F_^(g_.*(e_.+f_.*x_)))^n_.*(a_.+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
  (c+d*x)^m*(a+b*(F^(g*(e+f*x)))^n)^(p+1)/(b*f*g*n*(p+1)*Log[F]) - 
  d*m/(b*f*g*n*(p+1)*Log[F])*Int[(c+d*x)^(m-1)*(a+b*(F^(g*(e+f*x)))^n)^(p+1),x] /;
FreeQ[{F,a,b,c,d,e,f,g,m,n,p},x] && NeQ[p,-1]


Int[(c_.+d_.*x_)^m_.*(F_^(g_.*(e_.+f_.*x_)))^n_.*(a_.+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
  Unintegrable[(c+d*x)^m*(F^(g*(e+f*x)))^n*(a+b*(F^(g*(e+f*x)))^n)^p,x] /;
FreeQ[{F,a,b,c,d,e,f,g,m,n,p},x]


Int[(c_.+d_.*x_)^m_.*(k_.*G_^(j_.*(h_.+i_.*x_)))^q_.*(a_.+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
  (k*G^(j*(h+i*x)))^q/(F^(g*(e+f*x)))^n*Int[(c+d*x)^m*(F^(g*(e+f*x)))^n*(a+b*(F^(g*(e+f*x)))^n)^p,x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i,j,k,m,n,p,q},x] && EqQ[f*g*n*Log[F]-i*j*q*Log[G],0] && NeQ[(k*G^(j*(h+i*x)))^q-(F^(g*(e+f*x)))^n,0]





(* ::Subsection::Closed:: *)
(*2.3 Miscellaneous exponentials*)


Int[(F_^(c_.*(a_.+b_.*x_)))^n_.,x_Symbol] :=
  (F^(c*(a+b*x)))^n/(b*c*n*Log[F]) /;
FreeQ[{F,a,b,c,n},x]


Int[u_*F_^(c_.*v_),x_Symbol] :=
  Int[ExpandIntegrand[u*F^(c*ExpandToSum[v,x]),x],x] /;
FreeQ[{F,c},x] && PolynomialQ[u,x] && LinearQ[v,x] && $UseGamma===True


Int[u_*F_^(c_.*v_),x_Symbol] :=
  Int[ExpandIntegrand[F^(c*ExpandToSum[v,x]),u,x],x] /;
FreeQ[{F,c},x] && PolynomialQ[u,x] && LinearQ[v,x] && Not[$UseGamma===True]


Int[u_^m_.*F_^(c_.*v_)*w_,x_Symbol] :=
  With[{b=Coefficient[v,x,1],d=Coefficient[u,x,0],e=Coefficient[u,x,1],f=Coefficient[w,x,0],g=Coefficient[w,x,1]},
  g*u^(m+1)*F^(c*v)/(b*c*e*Log[F]) /;
 EqQ[e*g*(m+1)-b*c*(e*f-d*g)*Log[F],0]] /;
FreeQ[{F,c,m},x] && LinearQ[{u,v,w},x]


Int[w_*u_^m_.*F_^(c_.*v_),x_Symbol] :=
  Int[ExpandIntegrand[w*NormalizePowerOfLinear[u,x]^m*F^(c*ExpandToSum[v,x]),x],x] /;
FreeQ[{F,c},x] && PolynomialQ[w,x] && LinearQ[v,x] && PowerOfLinearQ[u,x] && IntegerQ[m] && $UseGamma===True


Int[w_*u_^m_.*F_^(c_.*v_),x_Symbol] :=
  Int[ExpandIntegrand[F^(c*ExpandToSum[v,x]),w*NormalizePowerOfLinear[u,x]^m,x],x] /;
FreeQ[{F,c},x] && PolynomialQ[w,x] && LinearQ[v,x] && PowerOfLinearQ[u,x] && IntegerQ[m] && Not[$UseGamma===True]


Int[w_*u_^m_.*F_^(c_.*v_),x_Symbol] :=
  Module[{uu=NormalizePowerOfLinear[u,x],z},
  z=If[PowerQ[uu] && FreeQ[uu[[2]],x], uu[[1]]^(m*uu[[2]]), uu^m];
  uu^m/z*Int[ExpandIntegrand[w*z*F^(c*ExpandToSum[v,x]),x],x]] /;
FreeQ[{F,c,m},x] && PolynomialQ[w,x] && LinearQ[v,x] && PowerOfLinearQ[u,x] && Not[IntegerQ[m]]


Int[F_^(c_.*(a_.+b_.*x_))*Log[d_.*x_]^n_.*(e_+h_.*(f_.+g_.*x_)*Log[d_.*x_]),x_Symbol] :=
  e*x*F^(c*(a+b*x))*Log[d*x]^(n+1)/(n+1) /;
FreeQ[{F,a,b,c,d,e,f,g,h,n},x] && EqQ[e-f*h*(n+1),0] && EqQ[g*h*(n+1)-b*c*e*Log[F],0] && NeQ[n,-1]


Int[x_^m_.*F_^(c_.*(a_.+b_.*x_))*Log[d_.*x_]^n_.*(e_+h_.*(f_.+g_.*x_)*Log[d_.*x_]),x_Symbol] :=
  e*x^(m+1)*F^(c*(a+b*x))*Log[d*x]^(n+1)/(n+1) /;
FreeQ[{F,a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*(m+1)-f*h*(n+1),0] && EqQ[g*h*(n+1)-b*c*e*Log[F],0] && NeQ[n,-1]


Int[F_^(a_.+b_.*(c_.+d_.*x_)),x_Symbol] :=
  F^(a+b*(c+d*x))/(b*d*Log[F]) /;
FreeQ[{F,a,b,c,d},x]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
  F^a*Sqrt[Pi]*Erfi[(c+d*x)*Rt[b*Log[F],2]]/(2*d*Rt[b*Log[F],2]) /;
FreeQ[{F,a,b,c,d},x] && PosQ[b]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
  F^a*Sqrt[Pi]*Erf[(c+d*x)*Rt[-b*Log[F],2]]/(2*d*Rt[-b*Log[F],2]) /;
FreeQ[{F,a,b,c,d},x] && NegQ[b]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)*F^(a+b*(c+d*x)^n)/d -
  b*n*Log[F]*Int[(c+d*x)^n*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d},x] && IntegerQ[2/n] && ILtQ[n,0]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  With[{k=Denominator[n]},
  k/d*Subst[Int[x^(k-1)*F^(a+b*x^(k*n)),x],x,(c+d*x)^(1/k)]] /;
FreeQ[{F,a,b,c,d},x] && IntegerQ[2/n] && Not[IntegerQ[n]]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  -F^a*(c+d*x)*Gamma[1/n,-b*(c+d*x)^n*Log[F]]/(d*n*(-b*(c+d*x)^n*Log[F])^(1/n)) /;
FreeQ[{F,a,b,c,d,n},x] && Not[IntegerQ[2/n]]


Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (e+f*x)^n*F^(a+b*(c+d*x)^n)/(b*f*n*(c+d*x)^n*Log[F]) /;
FreeQ[{F,a,b,c,d,e,f,n},x] && EqQ[m,n-1] && EqQ[d*e-c*f,0]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_)/(e_.+f_.*x_),x_Symbol] :=
  F^a*ExpIntegralEi[b*(c+d*x)^n*Log[F]]/(f*n) /;
FreeQ[{F,a,b,c,d,e,f,n},x] && EqQ[d*e-c*f,0]


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  1/(d*(m+1))*Subst[Int[F^(a+b*x^2),x],x,(c+d*x)^(m+1)] /;
FreeQ[{F,a,b,c,d,m,n},x] && EqQ[n,2*(m+1)]


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)^(m-n+1)*F^(a+b*(c+d*x)^n)/(b*d*n*Log[F]) -
  (m-n+1)/(b*n*Log[F])*Int[(c+d*x)^(m-n)*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d},x] && IntegerQ[2*(m+1)/n] && LtQ[0,(m+1)/n,5] && IntegerQ[n] && (LtQ[0,n,m+1] || LtQ[m,n,0])


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)^(m-n+1)*F^(a+b*(c+d*x)^n)/(b*d*n*Log[F]) -
  (m-n+1)/(b*n*Log[F])*Int[(c+d*x)^Simplify[m-n]*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d,m,n},x] && IntegerQ[2*Simplify[(m+1)/n]] && LtQ[0,Simplify[(m+1)/n],5] && Not[RationalQ[m]] && SumSimplerQ[m,-n]


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)^(m+1)*F^(a+b*(c+d*x)^n)/(d*(m+1)) -
  b*n*Log[F]/(m+1)*Int[(c+d*x)^(m+n)*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d},x] && IntegerQ[2*(m+1)/n] && LtQ[-4,(m+1)/n,5] && IntegerQ[n] && (GtQ[n,0] && LtQ[m,-1] || GtQ[-n,0] && LeQ[-n,m+1])


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)^(m+1)*F^(a+b*(c+d*x)^n)/(d*(m+1)) -
  b*n*Log[F]/(m+1)*Int[(c+d*x)^Simplify[m+n]*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d,m,n},x] && IntegerQ[2*Simplify[(m+1)/n]] && LtQ[-4,Simplify[(m+1)/n],5] && Not[RationalQ[m]] && SumSimplerQ[m,n]


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  With[{k=Denominator[n]},
  k/d*Subst[Int[x^(k*(m+1)-1)*F^(a+b*x^(k*n)),x],x,(c+d*x)^(1/k)]] /;
FreeQ[{F,a,b,c,d,m,n},x] && IntegerQ[2*(m+1)/n] && LtQ[0,(m+1)/n,5] && Not[IntegerQ[n]]


Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (e+f*x)^m/(c+d*x)^m*Int[(c+d*x)^m*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d,e,f,m,n},x] && EqQ[d*e-c*f,0] && IntegerQ[2*Simplify[(m+1)/n]] && NeQ[f,d] && Not[IntegerQ[m]] && NeQ[c*e,0]


Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
(*-F^a*(e+f*x)^(m+1)/(f*n)*ExpIntegralE[1-(m+1)/n,-b*(c+d*x)^n*Log[F]] *)
  -F^a*(e+f*x)^(m+1)/(f*n*(-b*(c+d*x)^n*Log[F])^((m+1)/n))*Gamma[(m+1)/n,-b*(c+d*x)^n*Log[F]] /;
FreeQ[{F,a,b,c,d,e,f,m,n},x] && EqQ[d*e-c*f,0]


Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
  f*(e+f*x)^(m-1)*F^(a+b*(c+d*x)^2)/(2*b*d^2*Log[F]) + 
  (d*e-c*f)/d*Int[(e+f*x)^(m-1)*F^(a+b*(c+d*x)^2),x] - 
  (m-1)*f^2/(2*b*d^2*Log[F])*Int[(e+f*x)^(m-2)*F^(a+b*(c+d*x)^2),x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && FractionQ[m] && GtQ[m,1]


Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
  f*(e+f*x)^(m+1)*F^(a+b*(c+d*x)^2)/((m+1)*f^2) + 
  2*b*d*(d*e-c*f)*Log[F]/(f^2*(m+1))*Int[(e+f*x)^(m+1)*F^(a+b*(c+d*x)^2),x] - 
  2*b*d^2*Log[F]/(f^2*(m+1))*Int[(e+f*x)^(m+2)*F^(a+b*(c+d*x)^2),x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && LtQ[m,-1]


Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (e+f*x)^(m+1)*F^(a+b*(c+d*x)^n)/(f*(m+1)) -
  b*d*n*Log[F]/(f*(m+1))*Int[(e+f*x)^(m+1)*(c+d*x)^(n-1)*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && IGtQ[n,2] && LtQ[m,-1]


Int[F_^(a_.+b_./(c_.+d_.*x_))/(e_.+f_.*x_),x_Symbol] :=
  d/f*Int[F^(a+b/(c+d*x))/(c+d*x),x] - 
  (d*e-c*f)/f*Int[F^(a+b/(c+d*x))/((c+d*x)*(e+f*x)),x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0]


Int[(e_.+f_.*x_)^m_*F_^(a_.+b_./(c_.+d_.*x_)),x_Symbol] :=
  (e+f*x)^(m+1)*F^(a+b/(c+d*x))/(f*(m+1)) + 
  b*d*Log[F]/(f*(m+1))*Int[(e+f*x)^(m+1)*F^(a+b/(c+d*x))/(c+d*x)^2,x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && ILtQ[m,-1]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_)/(e_.+f_.*x_),x_Symbol] :=
  Unintegrable[F^(a+b*(c+d*x)^n)/(e+f*x),x] /;
FreeQ[{F,a,b,c,d,e,f,n},x] && NeQ[d*e-c*f,0]


Int[u_^m_.*F_^v_,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F^ExpandToSum[v,x],x] /;
FreeQ[{F,m},x] && LinearQ[u,x] && BinomialQ[v,x] && Not[LinearMatchQ[u,x] && BinomialMatchQ[v,x]]


Int[u_*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  Int[ExpandLinearProduct[F^(a+b*(c+d*x)^n),u,c,d,x],x] /;
FreeQ[{F,a,b,c,d,n},x] && PolynomialQ[u,x]


Int[u_.*F_^(a_.+b_.*v_),x_Symbol] :=
  Int[u*F^(a+b*NormalizePowerOfLinear[v,x]),x] /;
FreeQ[{F,a,b},x] && PolynomialQ[u,x] && PowerOfLinearQ[v,x] && Not[PowerOfLinearMatchQ[v,x]]


(* Int[u_.*F_^(a_.+b_.*v_^n_),x_Symbol] :=
  Int[u*F^(a+b*ExpandToSum[v,x]^n),x] /;
FreeQ[{F,a,b,n},x] && PolynomialQ[u,x] && LinearQ[v,x] && Not[LinearMatchQ[v,x]] *)


(* Int[u_.*F_^u_,x_Symbol] :=
  Int[u*F^ExpandToSum[u,x],x] /;
FreeQ[F,x] && PolynomialQ[u,x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]] *)


Int[F_^(a_.+b_./(c_.+d_.*x_))/((e_.+f_.*x_)*(g_.+h_.*x_)),x_Symbol] :=
  -d/(f*(d*g-c*h))*Subst[Int[F^(a-b*h/(d*g-c*h)+d*b*x/(d*g-c*h))/x,x],x,(g+h*x)/(c+d*x)] /;
FreeQ[{F,a,b,c,d,e,f},x] && EqQ[d*e-c*f,0]


Int[(g_.+h_.*x_)^m_.*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
  F^(e+f*b/d)*Int[(g+h*x)^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,m},x] && EqQ[b*c-a*d,0]


Int[(g_.+h_.*x_)^m_.*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
  Int[(g+h*x)^m*F^((d*e+b*f)/d-f*(b*c-a*d)/(d*(c+d*x))),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,m},x] && NeQ[b*c-a*d,0] && EqQ[d*g-c*h,0]


Int[F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_))/(g_.+h_.*x_),x_Symbol] :=
  d/h*Int[F^(e+f*(a+b*x)/(c+d*x))/(c+d*x),x] - 
  (d*g-c*h)/h*Int[F^(e+f*(a+b*x)/(c+d*x))/((c+d*x)*(g+h*x)),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h},x] && NeQ[b*c-a*d,0] && NeQ[d*g-c*h,0]


Int[(g_.+h_.*x_)^m_*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
  (g+h*x)^(m+1)*F^(e+f*(a+b*x)/(c+d*x))/(h*(m+1)) - 
  f*(b*c-a*d)*Log[F]/(h*(m+1))*Int[(g+h*x)^(m+1)*F^(e+f*(a+b*x)/(c+d*x))/(c+d*x)^2,x] /;
FreeQ[{F,a,b,c,d,e,f,g,h},x] && NeQ[b*c-a*d,0] && NeQ[d*g-c*h,0] && ILtQ[m,-1]


Int[F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_))/((g_.+h_.*x_)*(i_.+j_.*x_)),x_Symbol] :=
  -d/(h*(d*i-c*j))*Subst[Int[F^(e+f*(b*i-a*j)/(d*i-c*j)-(b*c-a*d)*f*x/(d*i-c*j))/x,x],x,(i+j*x)/(c+d*x)] /;
FreeQ[{F,a,b,c,d,e,f,g,h},x] && EqQ[d*g-c*h,0]


Int[F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  F^(a-b^2/(4*c))*Int[F^((b+2*c*x)^2/(4*c)),x] /;
FreeQ[{F,a,b,c},x]


Int[F_^v_,x_Symbol] :=
  Int[F^ExpandToSum[v,x],x] /;
FreeQ[F,x] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[(d_.+e_.*x_)*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*F^(a+b*x+c*x^2)/(2*c*Log[F]) /;
FreeQ[{F,a,b,c,d,e},x] && EqQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m-1)*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
  (m-1)*e^2/(2*c*Log[F])*Int[(d+e*x)^(m-2)*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && EqQ[b*e-2*c*d,0] && GtQ[m,1]


Int[F_^(a_.+b_.*x_+c_.*x_^2)/(d_.+e_.*x_),x_Symbol] :=
  1/(2*e)*F^(a-b^2/(4*c))*ExpIntegralEi[(b+2*c*x)^2*Log[F]/(4*c)] /;
FreeQ[{F,a,b,c,d,e},x] && EqQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  (d+e*x)^(m+1)*F^(a+b*x+c*x^2)/(e*(m+1)) - 
  2*c*Log[F]/(e^2*(m+1))*Int[(d+e*x)^(m+2)*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && EqQ[b*e-2*c*d,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
  (b*e-2*c*d)/(2*c)*Int[F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m-1)*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*F^(a+b*x+c*x^2),x] -
  (m-1)*e^2/(2*c*Log[F])*Int[(d+e*x)^(m-2)*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && GtQ[m,1]


Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  (d+e*x)^(m+1)*F^(a+b*x+c*x^2)/(e*(m+1)) -
  (b*e-2*c*d)*Log[F]/(e^2*(m+1))*Int[(d+e*x)^(m+1)*F^(a+b*x+c*x^2),x] -
  2*c*Log[F]/(e^2*(m+1))*Int[(d+e*x)^(m+2)*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_.*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Unintegrable[(d+e*x)^m*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e,m},x]


Int[u_^m_.*F_^v_,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F^ExpandToSum[v,x],x] /;
FreeQ[{F,m},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[x_^m_.*F_^(e_.*(c_.+d_.*x_))*(a_.+b_.*F_^v_)^p_,x_Symbol] :=
  With[{u=IntHide[F^(e*(c+d*x))*(a+b*F^v)^p,x]},
  Dist[x^m,u,x] - m*Int[x^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e},x] && EqQ[v,2*e*(c+d*x)] && GtQ[m,0] && ILtQ[p,0]


Int[(F_^(e_.*(c_.+d_.*x_)))^n_.*(a_+b_.*(F_^(e_.*(c_.+d_.*x_)))^n_.)^p_.,x_Symbol] :=
  1/(d*e*n*Log[F])*Subst[Int[(a+b*x)^p,x],x,(F^(e*(c+d*x)))^n] /;
FreeQ[{F,a,b,c,d,e,n,p},x]


Int[(G_^(h_.(f_.+g_.*x_)))^m_.*(a_+b_.*(F_^(e_.*(c_.+d_.*x_)))^n_.)^p_.,x_Symbol] :=
  (G^(h*(f+g*x)))^m/(F^(e*(c+d*x)))^n*Int[(F^(e*(c+d*x)))^n*(a+b*(F^(e*(c+d*x)))^n)^p,x] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[d*e*n*Log[F],g*h*m*Log[G]]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  With[{m=FullSimplify[g*h*Log[G]/(d*e*Log[F])]},
  Denominator[m]*G^(f*h-c*g*h/d)/(d*e*Log[F])*Subst[Int[x^(Numerator[m]-1)*(a+b*x^Denominator[m])^p,x],x,F^(e*(c+d*x)/Denominator[m])] /;
 LeQ[m,-1] || GeQ[m,1]] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h,p},x]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  With[{m=FullSimplify[d*e*Log[F]/(g*h*Log[G])]},
  Denominator[m]/(g*h*Log[G])*Subst[Int[x^(Denominator[m]-1)*(a+b*F^(c*e-d*e*f/g)*x^Numerator[m])^p,x],x,G^(h*(f+g*x)/Denominator[m])] /;
 LtQ[m,-1] || GtQ[m,1]] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h,p},x]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  Int[Expand[G^(h*(f+g*x))*(a+b*F^(e*(c+d*x)))^p,x],x] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h},x] && IGtQ[p,0]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_,x_Symbol] :=
  a^p*G^(h*(f+g*x))/(g*h*Log[G])*Hypergeometric2F1[-p,g*h*Log[G]/(d*e*Log[F]),g*h*Log[G]/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h,p},x] && (ILtQ[p,0] || GtQ[a,0])


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_,x_Symbol] :=
  (a+b*F^(e*(c+d*x)))^p/(1+(b/a)*F^(e*(c+d*x)))^p*Int[G^(h*(f+g*x))*(1+b/a*F^(e*(c+d*x)))^p,x] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h,p},x] && Not[ILtQ[p,0] || GtQ[a,0]]


Int[G_^(h_. u_)*(a_+b_.*F_^(e_.*v_))^p_,x_Symbol] :=
  Int[G^(h*ExpandToSum[u,x])*(a+b*F^(e*ExpandToSum[v,x]))^p,x] /;
FreeQ[{F,G,a,b,e,h,p},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


(* Int[(c_.+d_.*x_)^m_.*F_^(g_.*(e_.+f_.*x_))/(a_+b_.*F_^(h_.*(e_.+f_.*x_))),x_Symbol] :=
  1/b*Int[(c+d*x)^m*F^((g-h)*(e+f*x)),x] - 
  a/b*Int[(c+d*x)^m*F^((g-h)*(e+f*x))/(a+b*F^(h*(e+f*x))),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,m},x] && LeQ[0,g/h-1,g/h] *)


(* Int[(c_.+d_.*x_)^m_.*F_^(g_.*(e_.+f_.*x_))/(a_+b_.*F_^(h_.*(e_.+f_.*x_))),x_Symbol] :=
  1/a*Int[(c+d*x)^m*F^(g*(e+f*x)),x] - 
  b/a*Int[(c+d*x)^m*F^((g+h)*(e+f*x))/(a+b*F^(h*(e+f*x))),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,m},x] && LeQ[g/h,g/h+1,0] *)


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*F_^u_)^p_.*(c_.+d_.*F_^v_)^q_.,x_Symbol] :=
  With[{w=ExpandIntegrand[(e+f*x)^m,(a+b*F^u)^p*(c+d*F^v)^q,x]},
  Int[w,x] /;
 SumQ[w]] /;
FreeQ[{F,a,b,c,d,e,f,m},x] && IntegersQ[p,q] && LinearQ[{u,v},x] && RationalQ[Simplify[u/v]]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  With[{m=FullSimplify[(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])]},
  Denominator[m]*G^(f*h-c*g*h/d)*H^(r*t-c*s*t/d)/(d*e*Log[F])*
    Subst[Int[x^(Numerator[m]-1)*(a+b*x^Denominator[m])^p,x],x,F^(e*(c+d*x)/Denominator[m])] /;
 RationalQ[m]] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t,p},x]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  G^((f-c*g/d)*h)*Int[H^(t*(r+s*x))*(b+a*F^(-e*(c+d*x)))^p,x] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && EqQ[d*e*p*Log[F]+g*h*Log[G],0] && IntegerQ[p]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  Int[Expand[G^(h*(f+g*x))*H^(t*(r+s*x))*(a+b*F^(e*(c+d*x)))^p,x],x] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && IGtQ[p,0]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_,x_Symbol] :=
  a^p*G^(h*(f+g*x))*H^(t*(r+s*x))/(g*h*Log[G]+s*t*Log[H])*
    Hypergeometric2F1[-p,(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F]),(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && ILtQ[p,0]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_,x_Symbol] :=
  G^(h*(f+g*x))*H^(t*(r+s*x))*(a+b*F^(e*(c+d*x)))^p/((g*h*Log[G]+s*t*Log[H])*((a+b*F^(e*(c+d*x)))/a)^p)*
    Hypergeometric2F1[-p,(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F]),(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t,p},x] && Not[IntegerQ[p]]


Int[G_^(h_. u_)*H_^(t_. w_)*(a_+b_.*F_^(e_.*v_))^p_,x_Symbol] :=
  Int[G^(h*ExpandToSum[u,x])*H^(t*ExpandToSum[w,x])*(a+b*F^(e*ExpandToSum[v,x]))^p,x] /;
FreeQ[{F,G,H,a,b,e,h,t,p},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[F_^(e_.*(c_.+d_.*x_))*(a_.*x_^n_.+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  (a*x^n+b*F^(e*(c+d*x)))^(p+1)/(b*d*e*(p+1)*Log[F]) - 
  a*n/(b*d*e*Log[F])*Int[x^(n-1)*(a*x^n+b*F^(e*(c+d*x)))^p,x] /;
FreeQ[{F,a,b,c,d,e,n,p},x] && NeQ[p,-1]


Int[x_^m_.*F_^(e_.*(c_.+d_.*x_))*(a_.*x_^n_.+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  x^m*(a*x^n+b*F^(e*(c+d*x)))^(p+1)/(b*d*e*(p+1)*Log[F]) - 
  a*n/(b*d*e*Log[F])*Int[x^(m+n-1)*(a*x^n+b*F^(e*(c+d*x)))^p,x] - 
  m/(b*d*e*(p+1)*Log[F])*Int[x^(m-1)*(a*x^n+b*F^(e*(c+d*x)))^(p+1),x] /;
FreeQ[{F,a,b,c,d,e,m,n,p},x] && NeQ[p,-1]


Int[(f_.+g_.*x_)^m_./(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[(f+g*x)^m/(b-q+2*c*F^u),x] - 2*c/q*Int[(f+g*x)^m/(b+q+2*c*F^u),x]] /;
FreeQ[{F,a,b,c,f,g},x] && EqQ[v,2*u] && LinearQ[u,x] && NeQ[b^2-4*a*c,0] && IGtQ[m,0]


Int[(f_.+g_.*x_)^m_.*F_^u_/(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[(f+g*x)^m*F^u/(b-q+2*c*F^u),x] - 2*c/q*Int[(f+g*x)^m*F^u/(b+q+2*c*F^u),x]] /;
FreeQ[{F,a,b,c,f,g},x] && EqQ[v,2*u] && LinearQ[u,x] && NeQ[b^2-4*a*c,0] && IGtQ[m,0]


Int[(f_.+g_.*x_)^m_.*(h_+i_.*F_^u_)/(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (Simplify[(2*c*h-b*i)/q]+i)*Int[(f+g*x)^m/(b-q+2*c*F^u),x] - 
  (Simplify[(2*c*h-b*i)/q]-i)*Int[(f+g*x)^m/(b+q+2*c*F^u),x]] /;
FreeQ[{F,a,b,c,f,g,h,i},x] && EqQ[v,2*u] && LinearQ[u,x] && NeQ[b^2-4*a*c,0] && IGtQ[m,0]


Int[x_^m_./(a_.*F_^(c_.+d_.*x_)+b_.*F_^v_),x_Symbol] :=
  With[{u=IntHide[1/(a*F^(c+d*x)+b*F^v),x]},
  x^m*u - m*Int[x^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d},x] && EqQ[v,-(c+d*x)] && GtQ[m,0]


Int[u_/(a_+b_.*F_^v_+c_.*F_^w_),x_Symbol] :=
  Int[u*F^v/(c+a*F^v+b*F^(2*v)),x] /;
FreeQ[{F,a,b,c},x] && EqQ[w,-v] && LinearQ[v,x] &&
  If[RationalQ[Coefficient[v,x,1]], GtQ[Coefficient[v,x,1],0], LtQ[LeafCount[v],LeafCount[w]]]


Int[F_^(g_.*(d_.+e_.*x_)^n_.)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[F^(g*(d+e*x)^n),1/(a+b*x+c*x^2),x],x] /;
FreeQ[{F,a,b,c,d,e,g,n},x]


Int[F_^(g_.*(d_.+e_.*x_)^n_.)/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[F^(g*(d+e*x)^n),1/(a+c*x^2),x],x] /;
FreeQ[{F,a,c,d,e,g,n},x]


Int[u_^m_.*F_^(g_.*(d_.+e_.*x_)^n_.)/(a_.+b_.*x_+c_*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[F^(g*(d+e*x)^n),u^m/(a+b*x+c*x^2),x],x] /;
FreeQ[{F,a,b,c,d,e,g,n},x] && PolynomialQ[u,x] && IntegerQ[m]


Int[u_^m_.*F_^(g_.*(d_.+e_.*x_)^n_.)/(a_+c_*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[F^(g*(d+e*x)^n),u^m/(a+c*x^2),x],x] /;
FreeQ[{F,a,c,d,e,g,n},x] && PolynomialQ[u,x] && IntegerQ[m]


Int[F_^((a_.+b_.*x_^4)/x_^2),x_Symbol] :=
  Sqrt[Pi]*Exp[2*Sqrt[-a*Log[F]]*Sqrt[-b*Log[F]]]*Erf[(Sqrt[-a*Log[F]]+Sqrt[-b*Log[F]]*x^2)/x]/
    (4*Sqrt[-b*Log[F]]) -
  Sqrt[Pi]*Exp[-2*Sqrt[-a*Log[F]]*Sqrt[-b*Log[F]]]*Erf[(Sqrt[-a*Log[F]]-Sqrt[-b*Log[F]]*x^2)/x]/
    (4*Sqrt[-b*Log[F]]) /;
FreeQ[{F,a,b},x]


Int[x_^m_.*(E^x_+x_^m_.)^n_,x_Symbol] :=
  -(E^x+x^m)^(n+1)/(n+1) +
  Int[(E^x+x^m)^(n+1),x] +
  m*Int[x^(m-1)*(E^x+x^m)^n,x] /;
RationalQ[m,n] && GtQ[m,0] && LtQ[n,0] && NeQ[n,-1]


Int[u_.*F_^(a_.*(v_.+b_.*Log[z_])),x_Symbol] :=
  Int[u*F^(a*v)*z^(a*b*Log[F]),x] /;
FreeQ[{F,a,b},x]


Int[F_^(d_.*(a_.+b_.*Log[c_.*x_^n_.]^2)),x_Symbol] :=
  x/(n*(c*x^n)^(1/n))*Subst[Int[E^(a*d*Log[F]+x/n+b*d*Log[F]*x^2),x],x,Log[c*x^n]] /;
FreeQ[{F,a,b,c,d,n},x]


Int[(e_.*x_)^m_.*F_^(d_.*(a_.+b_.*Log[c_.*x_^n_.]^2)),x_Symbol] :=
  (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n))*Subst[Int[E^(a*d*Log[F]+(m+1)*x/n+b*d*Log[F]*x^2),x],x,Log[c*x^n]] /;
FreeQ[{F,a,b,c,d,e,m,n},x]


Int[F_^(d_.*(a_.+b_.*Log[c_.*x_^n_.])^2),x_Symbol] :=
  Int[F^(a^2*d+2*a*b*d*Log[c*x^n]+b^2*d*Log[c*x^n]^2),x] /;
FreeQ[{F,a,b,c,d,n},x]


Int[(e_.*x_)^m_.*F_^(d_.*(a_.+b_.*Log[c_.*x_^n_.])^2),x_Symbol] :=
  Int[(e*x)^m*F^(a^2*d+2*a*b*d*Log[c*x^n]+b^2*d*Log[c*x^n]^2),x] /;
FreeQ[{F,a,b,c,d,e,m,n},x]


Int[Log[a_+b_.*(F_^(e_.*(c_.+d_.*x_)))^n_.],x_Symbol] :=
  1/(d*e*n*Log[F])*Subst[Int[Log[a+b*x]/x,x],x,(F^(e*(c+d*x)))^n] /;
FreeQ[{F,a,b,c,d,e,n},x] && GtQ[a,0]


Int[Log[a_+b_.*(F_^(e_.*(c_.+d_.*x_)))^n_.],x_Symbol] :=
  x*Log[a+b*(F^(e*(c+d*x)))^n] - b*d*e*n*Log[F]*Int[x*(F^(e*(c+d*x)))^n/(a+b*(F^(e*(c+d*x)))^n),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[GtQ[a,0]]


(* Int[u_.*(a_.*F_^v_)^n_,x_Symbol] :=
  a^n*Int[u*F^(n*v),x] /;
FreeQ[{F,a},x] && IntegerQ[n] *)


Int[u_.*(a_.*F_^v_)^n_,x_Symbol] :=
  (a*F^v)^n/F^(n*v)*Int[u*F^(n*v),x] /;
FreeQ[{F,a,n},x] && Not[IntegerQ[n]]


Int[u_,x_Symbol] :=
  With[{v=FunctionOfExponential[u,x]},
  v/D[v,x]*Subst[Int[FunctionOfExponentialFunction[u,x]/x,x],x,v]] /;
FunctionOfExponentialQ[u,x]


Int[u_.*(a_.*F_^v_+b_.*F_^w_)^n_,x_Symbol] :=
  Int[u*F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n,x] /;
FreeQ[{F,a,b,n},x] && ILtQ[n,0] && LinearQ[{v,w},x]


Int[u_.*(a_.*F_^v_+b_.*G_^w_)^n_,x_Symbol] :=
  Int[u*F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n,x] /;
FreeQ[{F,G,a,b,n},x] && ILtQ[n,0] && LinearQ[{v,w},x]


Int[u_.*(a_.*F_^v_+b_.*F_^w_)^n_,x_Symbol] :=
  (a*F^v+b*F^w)^n/(F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n)*Int[u*F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n,x] /;
FreeQ[{F,a,b,n},x] && Not[IntegerQ[n]] && LinearQ[{v,w},x]


Int[u_.*(a_.*F_^v_+b_.*G_^w_)^n_,x_Symbol] :=
  (a*F^v+b*G^w)^n/(F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n)*Int[u*F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n,x] /;
FreeQ[{F,G,a,b,n},x] && Not[IntegerQ[n]] && LinearQ[{v,w},x]


Int[u_.*F_^v_*G_^w_,x_Symbol] :=
  With[{z=v*Log[F]+w*Log[G]},
  Int[u*NormalizeIntegrand[E^z,x],x] /;
 BinomialQ[z,x] || PolynomialQ[z,x] && LeQ[Exponent[z,x],2]] /;
FreeQ[{F,G},x]


Int[F_^u_*(v_+w_)*y_.,x_Symbol] :=
  With[{z=v*y/(Log[F]*D[u,x])},
  F^u*z /;
 EqQ[D[z,x],w*y]] /;
FreeQ[F,x]


Int[F_^u_*v_^n_.*w_,x_Symbol] :=
  With[{z=Log[F]*v*D[u,x]+(n+1)*D[v,x]},
  Coefficient[w,x,Exponent[w,x]]/Coefficient[z,x,Exponent[z,x]]*F^u*v^(n+1) /;
 EqQ[Exponent[w,x],Exponent[z,x]] && EqQ[w*Coefficient[z,x,Exponent[z,x]],z*Coefficient[w,x,Exponent[w,x]]]] /;
FreeQ[{F,n},x] && PolynomialQ[u,x] && PolynomialQ[v,x] && PolynomialQ[w,x]


Int[(a_.+b_.*F_^(c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]))^n_./(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  2*e*g/(C*(e*f-d*g))*Subst[Int[(a+b*F^(c*x))^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
FreeQ[{a,b,c,d,e,f,g,A,B,C,F},x] && EqQ[C*d*f-A*e*g,0] && EqQ[B*e*g-C*(e*f+d*g),0] && IGtQ[n,0]


Int[(a_.+b_.*F_^(c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]))^n_./(A_+C_.*x_^2),x_Symbol] :=
  2*e*g/(C*(e*f-d*g))*Subst[Int[(a+b*F^(c*x))^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
FreeQ[{a,b,c,d,e,f,g,A,C,F},x] && EqQ[C*d*f-A*e*g,0] && EqQ[e*f+d*g,0] && IGtQ[n,0]


Int[(a_.+b_.*F_^(c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]))^n_/(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  Unintegrable[(a+b*F^(c*Sqrt[d+e*x]/Sqrt[f+g*x]))^n/(A+B*x+C*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g,A,B,C,F,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[B*e*g-C*(e*f+d*g),0] && Not[IGtQ[n,0]]


Int[(a_.+b_.*F_^(c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]))^n_/(A_+C_.*x_^2),x_Symbol] :=
  Unintegrable[(a+b*F^(c*Sqrt[d+e*x]/Sqrt[f+g*x]))^n/(A+C*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g,A,C,F,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[e*f+d*g,0] && Not[IGtQ[n,0]]



