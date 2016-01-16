(* ::Package:: *)

(* ::Section:: *)
(*Exponential Function Rules*)


(* ::Subsection::Closed:: *)
(*Exponential Functions*)


$UseGamma=False;


Int[F_^(c_.*(a_.+b_.*x_)),x_Symbol] :=
  F^(c*(a+b*x))/(b*c*Log[F]) /;
FreeQ[{F,a,b,c},x]


Int[(d_.+e_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_)),x_Symbol] :=
  (d+e*x)^m*F^(c*(a+b*x))/(b*c*Log[F]) - 
  e*m/(b*c*Log[F])*Int[(d+e*x)^(m-1)*F^(c*(a+b*x)),x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[2*m] && Not[$UseGamma===True] && m>0 (* && (IntegerQ[m] || m<2) *)


Int[F_^(c_.*(a_.+b_.*x_))/(d_.+e_.*x_),x_Symbol] :=
  1/e*F^(c*(a-b*d/e))*ExpIntegralEi[b*c*(d+e*x)*Log[F]/e] /;
FreeQ[{F,a,b,c,d,e},x] && Not[$UseGamma===True]


Int[F_^(c_.*(a_.+b_.*x_))/Sqrt[d_.+e_.*x_],x_Symbol] :=
  2/e*Subst[Int[F^(c*(a-b*d/e)+b*c*x^2/e),x],x,Sqrt[d+e*x]] /;
FreeQ[{F,a,b,c,d,e},x] && Not[$UseGamma===True]


Int[(d_.+e_.*x_)^m_*F_^(c_.*(a_.+b_.*x_)),x_Symbol] :=
  (d+e*x)^(m+1)*F^(c*(a+b*x))/(e*(m+1)) - 
  b*c*Log[F]/(e*(m+1))*Int[(d+e*x)^(m+1)*F^(c*(a+b*x)),x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[2*m] && Not[$UseGamma===True] && m<-1 (* && m>-3 *)


Int[(d_.+e_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_)),x_Symbol] :=
  (-e)^m*F^(c*(a-b*d/e))/(b^(m+1)*c^(m+1)*Log[F]^(m+1))*Gamma[m+1,-b*c*Log[F]/e*(d+e*x)] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[m] (* && $UseGamma===True *)


Int[(d_.+e_.*x_)^m_*F_^(c_.*(a_.+b_.*x_)),x_Symbol] :=
  (-e)^(m-1/2)*F^(c*(a-b*d/e))*Sqrt[d+e*x]/(b^(m+1/2)*c^(m+1/2)*Log[F]^(m+1/2)*Sqrt[(-b*c*Log[F]/e)*(d+e*x)])*
    Gamma[m+1,-b*c*Log[F]/e*(d+e*x)] /;
FreeQ[{F,a,b,c,d,e},x] && PositiveIntegerQ[m+1/2] (* && $UseGamma===True *)


Int[(d_.+e_.*x_)^m_*F_^(c_.*(a_.+b_.*x_)),x_Symbol] :=
  (-e)^(m+1/2)*F^(c*(a-b*d/e))*Sqrt[-b*c*Log[F]/e*(d+e*x)]/(b^(m+3/2)*c^(m+3/2)*Log[F]^(m+3/2)*Sqrt[d+e*x])*
    Gamma[m+1,-b*c*Log[F]/e*(d+e*x)] /;
FreeQ[{F,a,b,c,d,e},x] && NegativeIntegerQ[m-1/2] (* && $UseGamma===True *)


Int[(d_.+e_.*x_)^m_*E^(c_.*(a_.+b_.*x_)),x_Symbol] :=
  E^(c*(a-b*d/e))*(d+e*x)^m/(b*c*(-b*c/e*(d+e*x))^m)*Gamma[m+1,-b*c/e*(d+e*x)] /;
FreeQ[{a,b,c,d,e,m},x] (* && Not[IntegerQ[2*m]] *) && Not[SumSimplerQ[m,1]]


Int[(d_.+e_.*x_)^m_*F_^(c_.*(a_.+b_.*x_)),x_Symbol] :=
  -F^(c*(a-b*d/e))*(d+e*x)^(m+1)/(e*(-b*c*Log[F]*(d+e*x)/e)^(m+1))*Gamma[m+1,-b*c*Log[F]*(d+e*x)/e] /;
FreeQ[{F,a,b,c,d,e,m},x] (* && Not[IntegerQ[2*m]] *)


Int[u_^m_.*F_^(c_.*v_),x_Symbol] :=
  Int[NormalizePowerOfLinear[u,x]^m*F^(c*ExpandToSum[v,x]),x] /;
FreeQ[{F,c},x] && LinearQ[v,x] && PowerOfLinearQ[u,x] && Not[LinearMatchQ[v,x] && PowerOfLinearMatchQ[u,x]] && IntegerQ[m]


Int[u_^m_.*F_^(c_.*v_),x_Symbol] :=
  Module[{uu=NormalizePowerOfLinear[u,x],z},
  z=If[PowerQ[uu] && FreeQ[uu[[2]],x], uu[[1]]^(m*uu[[2]]), uu^m];
  uu^m/z*Int[z*F^(c*ExpandToSum[v,x]),x]] /; 
FreeQ[{F,c,m},x] && LinearQ[v,x] && PowerOfLinearQ[u,x] && Not[LinearMatchQ[v,x] && PowerOfLinearMatchQ[u,x]] && Not[IntegerQ[m]]


Int[u_*F_^(c_.*v_),x_Symbol] :=
  Int[ExpandIntegrand[u*F^(c*ExpandToSum[v,x]),x],x] /;
FreeQ[{F,c},x] && PolynomialQ[u,x] && LinearQ[v,x] && $UseGamma===True


Int[u_*F_^(c_.*v_),x_Symbol] :=
  Int[ExpandIntegrand[F^(c*ExpandToSum[v,x]),u,x],x] /;
FreeQ[{F,c},x] && PolynomialQ[u,x] && LinearQ[v,x] && Not[$UseGamma===True]


Int[u_^m_.*F_^(c_.*v_)*w_,x_Symbol] :=
  Coefficient[w,x,1]*u^(m+1)*F^(c*v)/(Coefficient[v,x,1]*c*Coefficient[u,x,1]*Log[F]) /;
FreeQ[{F,c,m},x] && LinearQ[{u,v,w},x] && 
  ZeroQ[Coefficient[u,x,1]*Coefficient[w,x,1]*(m+1)-
    Coefficient[v,x,1]*c*(Coefficient[u,x,1]*Coefficient[w,x,0]-Coefficient[u,x,0]*Coefficient[w,x,1])*Log[F]]


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
FreeQ[{F,a,b,c,d,e,f,g,h,n},x] && ZeroQ[e-f*h*(n+1)] && ZeroQ[g*h*(n+1)-b*c*e*Log[F]] && NonzeroQ[n+1]


Int[x_^m_.*F_^(c_.*(a_.+b_.*x_))*Log[d_.*x_]^n_.*(e_+h_.*(f_.+g_.*x_)*Log[d_.*x_]),x_Symbol] :=
  e*x^(m+1)*F^(c*(a+b*x))*Log[d*x]^(n+1)/(n+1) /;
FreeQ[{F,a,b,c,d,e,f,g,h,m,n},x] && ZeroQ[e*(m+1)-f*h*(n+1)] && ZeroQ[g*h*(n+1)-b*c*e*Log[F]] && NonzeroQ[n+1]


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
FreeQ[{F,a,b,c,d},x] && IntegerQ[2/n] && NegativeIntegerQ[n]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  Module[{k=Denominator[n]},
  k/d*Subst[Int[x^(k-1)*F^(a+b*x^(k*n)),x],x,(c+d*x)^(1/k)]] /;
FreeQ[{F,a,b,c,d},x] && IntegerQ[2/n] && Not[IntegerQ[n]]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  -F^a*(c+d*x)*Gamma[1/n,-b*(c+d*x)^n*Log[F]]/(d*n*(-b*(c+d*x)^n*Log[F])^(1/n)) /;
FreeQ[{F,a,b,c,d,n},x] && Not[IntegerQ[2/n]]


Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (e+f*x)^n*F^(a+b*(c+d*x)^n)/(b*f*n*(c+d*x)^n*Log[F]) /;
FreeQ[{F,a,b,c,d,e,f,n},x] && ZeroQ[m-(n-1)] && ZeroQ[d*e-c*f]


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_)/(e_.+f_.*x_),x_Symbol] :=
  F^a*ExpIntegralEi[b*(c+d*x)^n*Log[F]]/(f*n) /;
FreeQ[{F,a,b,c,d,e,f,n},x] && ZeroQ[d*e-c*f]


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  1/(d*(m+1))*Subst[Int[F^(a+b*x^2),x],x,(c+d*x)^(m+1)] /;
FreeQ[{F,a,b,c,d,m,n},x] && ZeroQ[n-2*(m+1)]


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)^(m-n+1)*F^(a+b*(c+d*x)^n)/(b*d*n*Log[F]) -
  (m-n+1)/(b*n*Log[F])*Int[(c+d*x)^(m-n)*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d},x] && RationalQ[m] && IntegerQ[2*(m+1)/n] && 0<(m+1)/n<5 && IntegerQ[n] && (0<n<m+1 || m<n<0)


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)^(m-n+1)*F^(a+b*(c+d*x)^n)/(b*d*n*Log[F]) -
  (m-n+1)/(b*n*Log[F])*Int[(c+d*x)^Simplify[m-n]*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d,m,n},x] && IntegerQ[2*Simplify[(m+1)/n]] && 0<Simplify[(m+1)/n]<5 && Not[RationalQ[m]] && SumSimplerQ[m,-n]


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)^(m+1)*F^(a+b*(c+d*x)^n)/(d*(m+1)) -
  b*n*Log[F]/(m+1)*Int[(c+d*x)^(m+n)*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d},x] && RationalQ[m] && IntegerQ[2*(m+1)/n] && -4<(m+1)/n<5 && IntegerQ[n] && (n>0 && m<-1 || 0<-n<=m+1)


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (c+d*x)^(m+1)*F^(a+b*(c+d*x)^n)/(d*(m+1)) -
  b*n*Log[F]/(m+1)*Int[(c+d*x)^Simplify[m+n]*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d,m,n},x] && IntegerQ[2*Simplify[(m+1)/n]] && -4<Simplify[(m+1)/n]<5 && Not[RationalQ[m]] && SumSimplerQ[m,n]


Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  Module[{k=Denominator[n]},
  k/d*Subst[Int[x^(k*(m+1)-1)*F^(a+b*x^(k*n)),x],x,(c+d*x)^(1/k)]] /;
FreeQ[{F,a,b,c,d},x] && RationalQ[m,n] && IntegerQ[2*(m+1)/n] && 0<(m+1)/n<5 && Not[IntegerQ[n]]


Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (e+f*x)^m/(c+d*x)^m*Int[(c+d*x)^m*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d,e,f,m,n},x] && ZeroQ[d*e-c*f] && IntegerQ[2*Simplify[(m+1)/n]] && NonzeroQ[f-d] && Not[IntegerQ[m]] && NonzeroQ[c*e]


Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
(*-F^a*(e+f*x)^(m+1)/(f*n)*ExpIntegralE[1-(m+1)/n,-b*(c+d*x)^n*Log[F]] *)
  -F^a*(e+f*x)^(m+1)/(f*n*(-b*(c+d*x)^n*Log[F])^((m+1)/n))*Gamma[(m+1)/n,-b*(c+d*x)^n*Log[F]] /;
FreeQ[{F,a,b,c,d,e,f,m,n},x] && ZeroQ[d*e-c*f]


Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
  f*(e+f*x)^(m-1)*F^(a+b*(c+d*x)^2)/(2*b*d^2*Log[F]) + 
  (d*e-c*f)/d*Int[(e+f*x)^(m-1)*F^(a+b*(c+d*x)^2),x] - 
  (m-1)*f^2/(2*b*d^2*Log[F])*Int[(e+f*x)^(m-2)*F^(a+b*(c+d*x)^2),x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && FractionQ[m] && m>1


Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
  f*(e+f*x)^(m+1)*F^(a+b*(c+d*x)^2)/((m+1)*f^2) + 
  2*b*d*(d*e-c*f)*Log[F]/(f^2*(m+1))*Int[(e+f*x)^(m+1)*F^(a+b*(c+d*x)^2),x] - 
  2*b*d^2*Log[F]/(f^2*(m+1))*Int[(e+f*x)^(m+2)*F^(a+b*(c+d*x)^2),x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && RationalQ[m] && m<-1


Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
  (e+f*x)^(m+1)*F^(a+b*(c+d*x)^n)/(f*(m+1)) -
  b*d*n*Log[F]/(f*(m+1))*Int[(e+f*x)^(m+1)*(c+d*x)^(n-1)*F^(a+b*(c+d*x)^n),x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && IntegerQ[n] && n>2 && RationalQ[m] && m<-1


Int[F_^(a_.+b_./(c_.+d_.*x_))/(e_.+f_.*x_),x_Symbol] :=
  d/f*Int[F^(a+b/(c+d*x))/(c+d*x),x] - 
  (d*e-c*f)/f*Int[F^(a+b/(c+d*x))/((c+d*x)*(e+f*x)),x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f]


Int[(e_.+f_.*x_)^m_*F_^(a_.+b_./(c_.+d_.*x_)),x_Symbol] :=
  (e+f*x)^(m+1)*F^(a+b/(c+d*x))/(f*(m+1)) + 
  b*d*Log[F]/(f*(m+1))*Int[(e+f*x)^(m+1)*F^(a+b/(c+d*x))/(c+d*x)^2,x] /;
FreeQ[{F,a,b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && IntegerQ[m] && m<-1


Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_)/(e_.+f_.*x_),x_Symbol] :=
  Defer[Int][F^(a+b*(c+d*x)^n)/(e+f*x),x] /;
FreeQ[{F,a,b,c,d,e,f,n},x] && NonzeroQ[d*e-c*f]


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
FreeQ[{F,a,b,c,d,e,f},x] && ZeroQ[d*e-c*f]


Int[(g_.+h_.*x_)^m_.*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
  F^(e+f*b/d)*Int[(g+h*x)^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,m},x] && ZeroQ[b*c-a*d]


Int[(g_.+h_.*x_)^m_.*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
  Int[(g+h*x)^m*F^((d*e+b*f)/d-f*(b*c-a*d)/(d*(c+d*x))),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,m},x] && NonzeroQ[b*c-a*d] && ZeroQ[d*g-c*h]


Int[F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_))/(g_.+h_.*x_),x_Symbol] :=
  d/h*Int[F^(e+f*(a+b*x)/(c+d*x))/(c+d*x),x] - 
  (d*g-c*h)/h*Int[F^(e+f*(a+b*x)/(c+d*x))/((c+d*x)*(g+h*x)),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h},x] && NonzeroQ[b*c-a*d] && NonzeroQ[d*g-c*h]


Int[(g_.+h_.*x_)^m_*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
  (g+h*x)^(m+1)*F^(e+f*(a+b*x)/(c+d*x))/(h*(m+1)) - 
  f*(b*c-a*d)*Log[F]/(h*(m+1))*Int[(g+h*x)^(m+1)*F^(e+f*(a+b*x)/(c+d*x))/(c+d*x)^2,x] /;
FreeQ[{F,a,b,c,d,e,f,g,h},x] && NonzeroQ[b*c-a*d] && NonzeroQ[d*g-c*h] && IntegerQ[m] && m<-1


Int[F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_))/((g_.+h_.*x_)*(i_.+j_.*x_)),x_Symbol] :=
  -d/(h*(d*i-c*j))*Subst[Int[F^(e+f*(b*i-a*j)/(d*i-c*j)-(b*c-a*d)*f*x/(d*i-c*j))/x,x],x,(i+j*x)/(c+d*x)] /;
FreeQ[{F,a,b,c,d,e,f,g,h},x] && ZeroQ[d*g-c*h]


Int[F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  F^(a-b^2/(4*c))*Int[F^((b+2*c*x)^2/(4*c)),x] /;
FreeQ[{F,a,b,c},x]


Int[F_^v_,x_Symbol] :=
  Int[F^ExpandToSum[v,x],x] /;
FreeQ[F,x] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[(d_.+e_.*x_)*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*F^(a+b*x+c*x^2)/(2*c*Log[F]) /;
FreeQ[{F,a,b,c,d,e},x] && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m-1)*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
  (m-1)*e^2/(2*c*Log[F])*Int[(d+e*x)^(m-2)*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && ZeroQ[b*e-2*c*d] && RationalQ[m] && m>1


Int[F_^(a_.+b_.*x_+c_.*x_^2)/(d_.+e_.*x_),x_Symbol] :=
  1/(2*e)*F^(a-b^2/(4*c))*ExpIntegralEi[(b+2*c*x)^2*Log[F]/(4*c)] /;
FreeQ[{F,a,b,c,d,e},x] && ZeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  (d+e*x)^(m+1)*F^(a+b*x+c*x^2)/(e*(m+1)) - 
  2*c*Log[F]/(e^2*(m+1))*Int[(d+e*x)^(m+2)*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && ZeroQ[b*e-2*c*d] && RationalQ[m] && m<-1


Int[(d_.+e_.*x_)*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
  (b*e-2*c*d)/(2*c)*Int[F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[b*e-2*c*d]


Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m-1)*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*F^(a+b*x+c*x^2),x] -
  (m-1)*e^2/(2*c*Log[F])*Int[(d+e*x)^(m-2)*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[b*e-2*c*d] && RationalQ[m] && m>1


Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  (d+e*x)^(m+1)*F^(a+b*x+c*x^2)/(e*(m+1)) -
  (b*e-2*c*d)*Log[F]/(e^2*(m+1))*Int[(d+e*x)^(m+1)*F^(a+b*x+c*x^2),x] -
  2*c*Log[F]/(e^2*(m+1))*Int[(d+e*x)^(m+2)*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NonzeroQ[b*e-2*c*d] && RationalQ[m] && m<-1


Int[(d_.+e_.*x_)^m_.*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Defer[Int][(d+e*x)^m*F^(a+b*x+c*x^2),x] /;
FreeQ[{F,a,b,c,d,e,m},x]


Int[u_^m_.*F_^v_,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F^ExpandToSum[v,x],x] /;
FreeQ[{F,m},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[x_^m_.*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(a+b*F^(e*(c+d*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e,m},x] && PositiveIntegerQ[n]


Int[(f_.+g_.*x_)^m_./(a_+b_.*F_^(e_.*(c_.+d_.*x_))),x_Symbol] :=
  (f+g*x)^(m+1)/(a*g*(m+1)) - 
  b/a*Int[(f+g*x)^m*F^(e*(c+d*x))/(a+b*F^(e*(c+d*x))),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && RationalQ[m] && m>0


Int[(f_.+g_.*x_)^m_.*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_,x_Symbol] :=
  Module[{u=IntHide[(a+b*F^(e*(c+d*x)))^n,x]},
  Dist[(f+g*x)^m,u,x] - 
  g*m*Int[(f+g*x)^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && RationalQ[m,n] && m>0 && n<-1


Int[(f_.+g_.*x_)^m_.*F_^(e_.*(c_.+d_.*x_))/(a_+b_.*F_^(e_.*(c_.+d_.*x_))),x_Symbol] :=
  (f+g*x)^m*Log[1+b*F^(e*(c+d*x))/a]/(b*d*e*Log[F]) - 
  g*m/(b*d*e*Log[F])*Int[(f+g*x)^(m-1)*Log[1+b/a*F^(e*(c+d*x))],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && RationalQ[m] && m>=1


Int[(f_.+g_.*x_)^m_.*F_^(e_.*(c_.+d_.*x_))*(a_.+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  (f+g*x)^m*(a+b*F^(e*(c+d*x)))^(p+1)/(b*d*e*(p+1)*Log[F]) - 
  g*m/(b*d*e*(p+1)*Log[F])*Int[(f+g*x)^(m-1)*(a+b*F^(e*(c+d*x)))^(p+1),x] /;
FreeQ[{F,a,b,c,d,e,f,g,m,p},x] && NonzeroQ[p+1]


Int[x_^m_.*F_^(e_.*(c_.+d_.*x_))*(a_.+b_.*F_^v_)^n_,x_Symbol] :=
  Module[{u=IntHide[F^(e*(c+d*x))*(a+b*F^v)^n,x]},
  Dist[x^m,u,x] - m*Int[x^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e},x] && ZeroQ[2*e*(c+d*x)-v] && RationalQ[m] && m>0 && NegativeIntegerQ[n]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_.,x_Symbol] :=
  Module[{m=FullSimplify[g*h*Log[G]/(d*e*Log[F])]},
  Denominator[m]*G^(f*h-c*g*h/d)/(d*e*Log[F])*Subst[Int[x^(Numerator[m]-1)*(a+b*x^Denominator[m])^n,x],x,F^(e*(c+d*x)/Denominator[m])] /;
 RationalQ[m] && Abs[m]>=1] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h,n},x]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_.,x_Symbol] :=
  Module[{m=FullSimplify[d*e*Log[F]/(g*h*Log[G])]},
  Denominator[m]/(g*h*Log[G])*Subst[Int[x^(Denominator[m]-1)*(a+b*F^(c*e-d*e*f/g)*x^Numerator[m])^n,x],x,G^(h*(f+g*x)/Denominator[m])] /;
 RationalQ[m] && Abs[m]>1] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h,n},x]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_.,x_Symbol] :=
  Int[Expand[G^(h*(f+g*x))*(a+b*F^(e*(c+d*x)))^n,x],x] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h},x] && Not[RationalQ[FullSimplify[g*h*Log[G]/(d*e*Log[F])]]] && PositiveIntegerQ[n]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_,x_Symbol] :=
  a^n*G^(h*(f+g*x))/(g*h*Log[G])*Hypergeometric2F1[-n,g*h*Log[G]/(d*e*Log[F]),g*h*Log[G]/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
FreeQ[{F,G,a,b,c,d,e,f,g,h},x] && Not[RationalQ[FullSimplify[g*h*Log[G]/(d*e*Log[F])]]] && NegativeIntegerQ[n]


Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_,x_Symbol] :=
  G^(h*(f+g*x))*(a+b*F^(e*(c+d*x)))^(n+1)/(a*g*h*Log[G])*
    Hypergeometric2F1[1,n+g*h*Log[G]/(d*e*Log[F])+1,g*h*Log[G]/(d*e*Log[F])+1,-b*F^(e*(c+d*x))/a] /;
(*G^(h*(f+g*x))*(a+b*F^(e*(c+d*x)))^n/(g*h*Log[G]*((a+b*F^(e*(c+d*x)))/a)^n)*
    Hypergeometric2F1[-n,g*h*Log[G]/(d*e*Log[F]),g*h*Log[G]/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /; *)
FreeQ[{F,G,a,b,c,d,e,f,g,h,n},x] && Not[RationalQ[FullSimplify[g*h*Log[G]/(d*e*Log[F])]]] && Not[IntegerQ[n]]


Int[G_^(h_. u_)*(a_+b_.*F_^(e_.*v_))^n_,x_Symbol] :=
  Int[G^(h*ExpandToSum[u,x])*(a+b*F^(e*ExpandToSum[v,x]))^n,x] /;
FreeQ[{F,G,a,b,e,h,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_.,x_Symbol] :=
  Module[{m=FullSimplify[(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])]},
  Denominator[m]*G^(f*h-c*g*h/d)*H^(r*t-c*s*t/d)/(d*e*Log[F])*
    Subst[Int[x^(Numerator[m]-1)*(a+b*x^Denominator[m])^n,x],x,F^(e*(c+d*x)/Denominator[m])] /;
 RationalQ[m]] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t,n},x]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_.,x_Symbol] :=
  G^((f-c*g/d)*h)*Int[H^(t*(r+s*x))*(b+a*F^(-e*(c+d*x)))^n,x] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && ZeroQ[d*e*n*Log[F]+g*h*Log[G]] && IntegerQ[n]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_.,x_Symbol] :=
  Int[Expand[G^(h*(f+g*x))*H^(t*(r+s*x))*(a+b*F^(e*(c+d*x)))^n,x],x] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && Not[RationalQ[FullSimplify[(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])]]] && PositiveIntegerQ[n]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_,x_Symbol] :=
  a^n*G^(h*(f+g*x))*H^(t*(r+s*x))/(g*h*Log[G]+s*t*Log[H])*
    Hypergeometric2F1[-n,(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F]),(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && Not[RationalQ[FullSimplify[(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])]]] && NegativeIntegerQ[n]


Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^n_,x_Symbol] :=
  G^(h*(f+g*x))*H^(t*(r+s*x))*(a+b*F^(e*(c+d*x)))^n/((g*h*Log[G]+s*t*Log[H])*((a+b*F^(e*(c+d*x)))/a)^n)*
    Hypergeometric2F1[-n,(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F]),(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t,n},x] && Not[RationalQ[FullSimplify[(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])]]] && Not[IntegerQ[n]]


Int[G_^(h_. u_)*H_^(t_. w_)*(a_+b_.*F_^(e_.*v_))^n_,x_Symbol] :=
  Int[G^(h*ExpandToSum[u,x])*H^(t*ExpandToSum[w,x])*(a+b*F^(e*ExpandToSum[v,x]))^n,x] /;
FreeQ[{F,G,H,a,b,e,h,t,n},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[F_^(e_.*(c_.+d_.*x_))*(a_.*x_^n_.+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  (a*x^n+b*F^(e*(c+d*x)))^(p+1)/(b*d*e*(p+1)*Log[F]) - 
  a*n/(b*d*e*Log[F])*Int[x^(n-1)*(a*x^n+b*F^(e*(c+d*x)))^p,x] /;
FreeQ[{F,a,b,c,d,e,n,p},x] && NonzeroQ[p+1]


Int[x_^m_.*F_^(e_.*(c_.+d_.*x_))*(a_.*x_^n_.+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
  x^m*(a*x^n+b*F^(e*(c+d*x)))^(p+1)/(b*d*e*(p+1)*Log[F]) - 
  a*n/(b*d*e*Log[F])*Int[x^(m+n-1)*(a*x^n+b*F^(e*(c+d*x)))^p,x] - 
  m/(b*d*e*(p+1)*Log[F])*Int[x^(m-1)*(a*x^n+b*F^(e*(c+d*x)))^(p+1),x] /;
FreeQ[{F,a,b,c,d,e,m,n,p},x] && NonzeroQ[p+1]


Int[(f_.+g_.*x_)^m_./(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[(f+g*x)^m/(b-q+2*c*F^u),x] - 
  2*c/q*Int[(f+g*x)^m/(b+q+2*c*F^u),x] /;
 NonzeroQ[q]] /;
FreeQ[{F,a,b,c,f,g},x] && ZeroQ[v-2*u] && LinearQ[u,x] && PositiveIntegerQ[m]


Int[(f_.+g_.*x_)^m_.*(d_.+e_.*F_^u_)/(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (Simplify[(2*c*d-b*e)/q]+e)*Int[(f+g*x)^m/(b-q+2*c*F^u),x] - 
  (Simplify[(2*c*d-b*e)/q]-e)*Int[(f+g*x)^m/(b+q+2*c*F^u),x] /;
 NonzeroQ[q]] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && ZeroQ[v-2*u] && LinearQ[u,x] && PositiveIntegerQ[m]


Int[x_^m_./(a_.*F_^(c_.+d_.*x_)+b_.*F_^v_),x_Symbol] :=
  Module[{u=IntHide[1/(a*F^(c+d*x)+b*F^v),x]},
  x^m*u - m*Int[x^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d},x] && ZeroQ[(c+d*x)+v] && RationalQ[m] && m>0


Int[u_/(a_+b_.*F_^v_+c_.*F_^w_),x_Symbol] :=
  Int[u*F^v/(c+a*F^v+b*F^(2*v)),x] /;
FreeQ[{F,a,b,c},x] && LinearQ[v,x] && LinearQ[w,x] && ZeroQ[v+w] &&
  If[RationalQ[Coefficient[v,x,1]], Coefficient[v,x,1]>0, LeafCount[v]<LeafCount[w]]


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
RationalQ[m,n] && m>0 && n<0 && n!=-1


Int[Log[d_+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  x*Log[d+e*(F^(c*(a+b*x)))^n] - 
  x*Log[1+e/d*(F^(c*(a+b*x)))^n] + 
  Int[Log[1+e/d*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,d,e,n},x] && NonzeroQ[d-1]


(* Int[u_.*(a_.*F_^v_)^n_,x_Symbol] :=
  a^n*Int[u*F^(n*v),x] /;
FreeQ[{F,a},x] && IntegerQ[n] *)


Int[u_.*(a_.*F_^v_)^n_,x_Symbol] :=
  (a*F^v)^n/F^(n*v)*Int[u*F^(n*v),x] /;
FreeQ[{F,a,n},x] && Not[IntegerQ[n]]


Int[u_,x_Symbol] :=
  Module[{v=FunctionOfExponential[u,x]},
  v/D[v,x]*Subst[Int[FunctionOfExponentialFunction[u,x]/x,x],x,v]] /;
FunctionOfExponentialQ[u,x]


Int[u_.*(a_.*F_^v_+b_.*F_^w_)^n_,x_Symbol] :=
  Int[u*F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n,x] /;
FreeQ[{F,a,b,n},x] && NegativeIntegerQ[n] && LinearQ[{v,w},x]


Int[u_.*(a_.*F_^v_+b_.*G_^w_)^n_,x_Symbol] :=
  Int[u*F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n,x] /;
FreeQ[{F,G,a,b,n},x] && NegativeIntegerQ[n] && LinearQ[{v,w},x]


Int[u_.*(a_.*F_^v_+b_.*F_^w_)^n_,x_Symbol] :=
  (a*F^v+b*F^w)^n/(F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n)*Int[u*F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n,x] /;
FreeQ[{F,a,b,n},x] && Not[IntegerQ[n]] && LinearQ[{v,w},x]


Int[u_.*(a_.*F_^v_+b_.*G_^w_)^n_,x_Symbol] :=
  (a*F^v+b*G^w)^n/(F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n)*Int[u*F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n,x] /;
FreeQ[{F,G,a,b,n},x] && Not[IntegerQ[n]] && LinearQ[{v,w},x]


Int[u_.*F_^v_*G_^w_,x_Symbol] :=
  Int[u*NormalizeIntegrand[E^(v*Log[F]+w*Log[G]),x],x] /;
FreeQ[{F,G},x] && (BinomialQ[v+w,x] || PolynomialQ[v+w,x] && Exponent[v+w,x]<=2)


Int[F_^u_*(v_+w_)*y_.,x_Symbol] :=
  Module[{z=v*y/(Log[F]*D[u,x])},
  F^u*z /;
 ZeroQ[D[z,x]-w*y]] /;
FreeQ[F,x]


Int[F_^u_*v_^n_.*w_,x_Symbol] :=
  Module[{z=Log[F]*v*D[u,x]+(n+1)*D[v,x]},
  Coefficient[w,x,Exponent[w,x]]/Coefficient[z,x,Exponent[z,x]]*F^u*v^(n+1) /;
 Exponent[w,x]==Exponent[z,x] && ZeroQ[w*Coefficient[z,x,Exponent[z,x]]-z*Coefficient[w,x,Exponent[w,x]]]] /;
FreeQ[{F,n},x] && PolynomialQ[u,x] && PolynomialQ[v,x] && PolynomialQ[w,x]


(* ::Subsection::Closed:: *)
(*u (a+b log(c (d (e+f x)^p)^q))^n*)


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
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[f*g-e*h] && NonzeroQ[m+1]


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
  Module[{u=IntHide[(i+j*x)^m/(g+h*x),x]},
  Dist[a+b*Log[c*(d*(e+f*x)^p)^q],u] - b*h*p*q*Int[SimplifyIntegrand[u/(g+h*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q},x] && ZeroQ[f*g-e*h] && IntegerQ[m+1/2]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(g_.+h_.*x_+i_.*x_^2),x_Symbol] :=
  e*f*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/((e+f*x)*(f*g+e*i*x)),x] /;
FreeQ[{a,b,c,e,f,g,h,i,p,q},x] && ZeroQ[f^2*g-e*f*h+e^2*i]


Int[(a_.+b_.*Log[c_.*(d_.*(e_+f_.*x_)^p_.)^q_.])/(g_+i_.*x_^2),x_Symbol] :=
  e*f*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/((e+f*x)*(f*g+e*i*x)),x] /;
FreeQ[{a,b,c,e,f,g,i,p,q},x] && ZeroQ[f^2*g+e^2*i]


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(e_.+f_.*x_)])^n_./(g_.+h_.*x_),x_Symbol] :=
  1/(c^m*f^m*h)*Subst[Int[(a+b*x)^n*(c*f*i-c*e*j+j*E^x)^m,x],x,Log[c*(e+f*x)]] /;
FreeQ[{a,b,c,e,f,g,h,i,j,n},x] && ZeroQ[f*g-e*h] && PositiveIntegerQ[m] && (IntegerQ[n] || m>0)


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  Module[{u=ExpandIntegrand[(a+b*Log[c*(d*(e+f*x)^p)^q])^n,(i+j*x)^m/(g+h*x),x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q},x] && IntegerQ[m] && PositiveIntegerQ[n]


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  Defer[Int][(i+j*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/(g+h*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n,p,q},x]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/Sqrt[g_+h_.*x_^2],x_Symbol] :=
  Module[{u=IntHide[1/Sqrt[g+h*x^2],x]},  
  Dist[(a+b*Log[c*(d*(e+f*x)^p)^q]),u] - b*f*p*q*Int[SimplifyIntegrand[u/(e+f*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && PositiveQ[g]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/Sqrt[g_+h_.*x_^2],x_Symbol] :=
  Sqrt[1+h/g*x^2]/Sqrt[g+h*x^2]*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/Sqrt[1+h/g*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && Not[PositiveQ[g]]


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
  Module[{u=IntHide[Px*F[g+h*x]^m,x]},
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
  Module[{u=IntHide[1/(d+e*x^2),x]},  
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
  Module[{u=ExpandIntegrand[(a+b*Log[c*(d*(e+f*x)^p)^q])^n,RFx,x]},
  Int[u,x] /;
 SumQ[u] || SumQ[u=ExpandIntegrand[RFx*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x]]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[RFx_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  Defer[Int][RFx*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x] /;
FreeQ[{a,b,c,d,e,f,n,p,q},x] && RationalFunctionQ[RFx,x]


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
(*u log(e ((a+b x) (c+d x)^-1)^n)^p*)


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


Int[Log[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]/((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  1/(d*f-c*g)*PolyLog[2,Simplify[(c-a*e)*(f+g*x)/(f*(c+d*x))]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*f-a*g] && NonzeroQ[d*f-c*g] && ZeroQ[d*f-c*g-e*(b*f-a*g)]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  -1/(d*f-c*g)*Log[(b*c-a*d)*(f+g*x)/((b*f-a*g)*(c+d*x))]*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p + 
  n*n1*p*(b*c-a*d)/(d*f-c*g)*
    Int[(1/((a+b*x)*(c+d*x)))*Log[(b*c-a*d)*(f+g*x)/((b*f-a*g)*(c+d*x))]*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[b*f-a*g] && NonzeroQ[d*f-c*g] && 
  PositiveIntegerQ[p]


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
  Module[{f=Simplify[(1-v)/u]},
  Log[v]/(n*(p+1)*(b*c-a*d))*Log[e*u^n]^(p+1) + 
  f/(n*(p+1))*Int[1/((c+d*x)*(c-a*f+(d-b*f)))*Log[e*u^n]^(p+1),x]] /;
FreeQ[{a,b,c,d,e,n,Simplify[u/(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[u_]^p_*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  Module[{f=Simplify[(1-v)/u]},
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
  Module[{f=Simplify[u*(1-v)]},
  Log[v]/(n*(p+1)*(b*c-a*d))*Log[e*u^n]^(p+1) - 
  f/(n*(p+1))*Int[1/((a+b*x)*(a-c*f+(b-d*f)))*Log[e*u^n]^(p+1),x]] /;
FreeQ[{a,b,c,d,e,n,Simplify[u*(1-v)],Simplify[u*(c+d*x)/(a+b*x)]},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[Log[u_]^p_*Log[v_]/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  Module[{f=Simplify[u*(1-v)]},
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
  Module[{u=IntHide[1/(f+g*x+h*x^2),x]},  
  u*Log[e*(e1*(a+b*x)^n1*(c+d*x)^n2)^n] - n*(b*c-a*d)*Int[u/((a+b*x)*(c+d*x)),x]] /;
FreeQ[{a,b,c,d,e,e1,f,g,h,n,n1},x] && ZeroQ[n1+n2]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]/(f_+h_.*x_^2),x_Symbol] :=
  Module[{u=IntHide[1/(f+h*x^2),x]},  
  u*Log[e*(e1*(a+b*x)^n1*(c+d*x)^n2)^n] - n*(b*c-a*d)*Int[u/((a+b*x)*(c+d*x)),x]] /;
FreeQ[{a,b,c,d,e,e1,f,h,n,n1},x] && ZeroQ[n1+n2]


Int[RFx_*Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_.,x_Symbol] :=
  Module[{u=ExpandIntegrand[Log[e*(e1*(a+b*x)^n1*(c+d*x)^n2)^n]^p,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n,e1,n1},x] && ZeroQ[n1+n2] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[p]


Int[u_.*Log[v_]^p_.,x_Symbol] :=
  Module[{lst=QuotientOfLinearsParts[v,x]},
  Int[u*Log[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^p,x] /;
 Not[OneQ[p] && ZeroQ[lst[[3]]]]] /;
FreeQ[p,x] && QuotientOfLinearsQ[v,x] && Not[QuotientOfLinearsMatchQ[v,x]]


(* ::Subsection::Closed:: *)
(*Logarithm Functions*)


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
  Module[{w=IntHide[ArcSin[f+g*x]^m,x]},  
  Dist[a+b*Log[c*(d+e*x^n)^p],w,x] - 
  b*e*n*p*Int[SimplifyIntegrand[x^(n-1)*w/(d+e*x^n),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && PositiveIntegerQ[m]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_^2)^p_.])/(f_.+g_.*x_^2),x_Symbol] :=
  Module[{u=IntHide[1/(f+g*x^2),x]},  
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
  Module[{w=DerivativeDivides[v,u*(1-v),x]},
  w*PolyLog[2,Together[1-v]] /;
 Not[FalseQ[w]]]


Int[(a_.+b_.*Log[u_])*Log[v_]*w_,x_Symbol] :=
  Module[{z=DerivativeDivides[v,w*(1-v),x]},
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
  Module[{u=IntHide[1/(d+e*x^2),x]},  
  u*Log[c*RFx^n] - n*Int[SimplifyIntegrand[u*D[RFx,x]/RFx,x],x]] /;
FreeQ[{c,d,e,n},x] && RationalFunctionQ[RFx,x] && Not[PolynomialQ[RFx,x]]


Int[Log[c_.*Px_^n_.]/Qx_,x_Symbol] :=
  Module[{u=IntHide[1/Qx,x]},  
  u*Log[c*Px^n] - n*Int[SimplifyIntegrand[u*D[Px,x]/Px,x],x]] /;
FreeQ[{c,n},x] && QuadraticQ[{Qx,Px},x] && ZeroQ[D[Px/Qx,x]]


Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  Module[{u=ExpandIntegrand[(a+b*Log[c*RFx^p])^n,RGx,x]},
  Int[u,x] /;
 SumQ[u] || SumQ[u=ExpandIntegrand[RGx*(a+b*Log[c*RFx^p])^n,x]]] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && PositiveIntegerQ[n]


Int[RFx_*(a_.+b_.*Log[u_]),x_Symbol] :=
  Module[{lst=SubstForFractionalPowerOfLinear[RFx*(a+b*Log[u]),x]},
  lst[[2]]*lst[[4]]*Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])] /;
 NotFalseQ[lst]] /;
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


Int[Log[u_],x_Symbol] :=
  x*Log[u] - Int[SimplifyIntegrand[x*D[u,x]/u,x],x] /;
InverseFunctionFreeQ[u,x]


Int[Log[u_]/(a_.+b_.*x_),x_Symbol] :=
  Log[a+b*x]*Log[u]/b -
  1/b*Int[SimplifyIntegrand[Log[a+b*x]*D[u,x]/u,x],x] /;
FreeQ[{a,b},x] && RationalFunctionQ[D[u,x]/u,x] && (NonzeroQ[a] || Not[BinomialTest[u,x] && BinomialTest[u,x][[3]]^2===1])


Int[(a_.+b_.*x_)^m_.*Log[u_],x_Symbol] :=
  (a+b*x)^(m+1)*Log[u]/(b*(m+1)) - 
  1/(b*(m+1))*Int[SimplifyIntegrand[(a+b*x)^(m+1)*D[u,x]/u,x],x] /;
FreeQ[{a,b,m},x] && InverseFunctionFreeQ[u,x] && NonzeroQ[m+1] (* && Not[FunctionOfQ[x^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]] *)


Int[Log[u_]/Qx_,x_Symbol] :=
  Module[{v=IntHide[1/Qx,x]},  
  v*Log[u] - Int[SimplifyIntegrand[v*D[u,x]/u,x],x]] /;
QuadraticQ[Qx,x] && InverseFunctionFreeQ[u,x]


(* Int[x_^m_.*Px_.*Log[u_],x_Symbol] :=
  Module[{v=IntHide[x^m*Px,x]},  
  Dist[Log[u],v] - Int[SimplifyIntegrand[v*D[u,x]/u,x],x]] /;
FreeQ[m,x] && PolynomialQ[Px,x] && InverseFunctionFreeQ[u,x] *)


Int[u_^(a_.*x_)*Log[u_],x_Symbol] :=
  u^(a*x)/a - Int[SimplifyIntegrand[x*u^(a*x-1)*D[u,x],x],x] /;
FreeQ[a,x] && InverseFunctionFreeQ[u,x]


Int[v_*Log[u_],x_Symbol] :=
  Module[{w=IntHide[v,x]},  
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
  Module[{z=IntHide[u,x]},  
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
  Module[{lst=FunctionOfLog[u,x]},
  ShowStep["","Int[f[Log[a*x^n]]/x,x]","Subst[Int[f[x],x],x,Log[a*x^n]]/n",Hold[
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]] /;
 Not[FalseQ[lst]]] /;
SimplifyFlag && NonsumQ[u],

Int[u_/x_,x_Symbol] :=
  Module[{lst=FunctionOfLog[u,x]},
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
 Not[FalseQ[lst]]] /;
NonsumQ[u]] *)


If[ShowSteps,

Int[u_,x_Symbol] :=
  Module[{lst=FunctionOfLog[Cancel[x*u],x]},
  ShowStep["","Int[f[Log[a*x^n]]/x,x]","Subst[Int[f[x],x],x,Log[a*x^n]]/n",Hold[
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]] /;
 Not[FalseQ[lst]]] /;
SimplifyFlag && NonsumQ[u],

Int[u_,x_Symbol] :=
  Module[{lst=FunctionOfLog[Cancel[x*u],x]},
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
 Not[FalseQ[lst]]] /;
NonsumQ[u]]


Int[u_.*Log[Gamma[v_]],x_Symbol] :=
  (Log[Gamma[v]]-LogGamma[v])*Int[u,x] + Int[u*LogGamma[v],x]


Int[u_.*(a_. w_+b_. w_*Log[v_]^n_.)^p_.,x_Symbol] :=
  Int[u*w^p*(a+b*Log[v]^n)^p,x] /;
FreeQ[{a,b,n},x] && IntegerQ[p]
