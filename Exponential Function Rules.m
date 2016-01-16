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
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(a+b*F^(e*(c+d*x)))^n,x]]},
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
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[F^(e*(c+d*x))*(a+b*F^v)^n,x]]},
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


Int[x_^m_./(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[x^m/(b-q+2*c*F^u),x] - 
  2*c/q*Int[x^m/(b+q+2*c*F^u),x] /;
 NonzeroQ[q]] /;
FreeQ[{F,a,b,c},x] && ZeroQ[v-2*u] && LinearQ[u,x] && PositiveIntegerQ[m]


Int[x_^m_.*F_^u_/(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (1-b/q)*Int[x^m/(b-q+2*c*F^u),x] + 
  (1+b/q)*Int[x^m/(b+q+2*c*F^u),x] /;
 NonzeroQ[q]] /;
FreeQ[{F,a,b,c},x] && ZeroQ[v-2*u] && LinearQ[u,x] && PositiveIntegerQ[m]


Int[x_^m_./(a_.*F_^(c_.+d_.*x_)+b_.*F_^v_),x_Symbol] :=
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[1/(a*F^(c+d*x)+b*F^v),x]]},
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
(*Logarithm Functions*)


Int[Log[c_.*(d_.+e_.*x_)^n_.],x_Symbol] :=
  -n*x + (d+e*x)*Log[c*(d+e*x)^n]/e /;
FreeQ[{c,d,e,n},x]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
  (d+e*x)*(a+b*Log[c*(d+e*x)^n])^p/e -
  b*n*p*Int[(a+b*Log[c*(d+e*x)^n])^(p-1),x] /;
FreeQ[{a,b,c,d,e,n},x] && RationalQ[p] && p>0


Int[1/Log[c_.*(a_.+b_.*x_)],x_Symbol] :=
  LogIntegral[c*(a+b*x)]/(c*b) /;
FreeQ[{a,b,c},x]


Int[1/(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]),x_Symbol] :=
  (d+e*x)/(b*e*n*E^(a/(b*n))*(c*(d+e*x)^n)^(1/n))*ExpIntegralEi[(a+b*Log[c*(d+e*x)^n])/(b*n)] /;
FreeQ[{a,b,c,d,e,n},x]


Int[1/Sqrt[a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]],x_Symbol] :=
  Sqrt[Pi]*Rt[b*n,2]*(d+e*x)/(b*e*n*E^(a/(b*n))*(c*(d+e*x)^n)^(1/n))*Erfi[Sqrt[a+b*Log[c*(d+e*x)^n]]/Rt[b*n,2]] /;
FreeQ[{a,b,c,d,e,n},x] && PosQ[b*n]


Int[1/Sqrt[a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]],x_Symbol] :=
  Sqrt[Pi]*Rt[-b*n,2]*(d+e*x)/(b*e*n*E^(a/(b*n))*(c*(d+e*x)^n)^(1/n))*Erf[Sqrt[a+b*Log[c*(d+e*x)^n]]/Rt[-b*n,2]] /;
FreeQ[{a,b,c,d,e,n},x] && NegQ[b*n]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
  (d+e*x)*(a+b*Log[c*(d+e*x)^n])^(p+1)/(b*e*n*(p+1)) -
  1/(b*n*(p+1))*Int[(a+b*Log[c*(d+e*x)^n])^(p+1),x] /;
FreeQ[{a,b,c,d,e,n},x] && RationalQ[p] && p<-1


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
  (d+e*x)*(a+b*Log[c*(d+e*x)^n])^p/(e*E^(a/(b*n))*(c*(d+e*x)^n)^(1/n)*(-(a+b*Log[c*(d+e*x)^n])/(b*n))^p)*
    Gamma[p+1,-(a+b*Log[c*(d+e*x)^n])/(b*n)] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[2*p]]


Int[x_^q1_*(a_.+b_.*Log[c_.*(d_.+e_.*x_^q_)^n_.])^p_.,x_Symbol] :=
  1/q*Subst[Int[(a+b*Log[c*(d+e*x)^n])^p,x],x,x^q] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && ZeroQ[q1-(q-1)]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_./(f_.+g_.*x_),x_Symbol] :=
  1/(g*n)*Subst[Int[(a+b*x)^p,x],x,Log[c*(d+e*x)^n]] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && ZeroQ[e*f-d*g]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_.,x_Symbol] :=
  (f+g*x)^(m+1)*(a+b*Log[c*(d+e*x)^n])^p/(g*(m+1)) - 
  b*n*p/(m+1)*Int[(f+g*x)^m*(a+b*Log[c*(d+e*x)^n])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f-d*g] && NonzeroQ[m+1] && RationalQ[p] && p>0


Int[(f_.+g_.*x_)^m_./(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]),x_Symbol] :=
  (f+g*x)^(m+1)/(b*g*n*E^((a*(m+1))/(b*n))*(c*(d+e*x)^n)^((m+1)/n))*
    ExpIntegralEi[(m+1)*(a+b*Log[c*(d+e*x)^n])/(b*n)] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f-d*g] && NonzeroQ[m+1]


Int[(f_.+g_.*x_)^m_./Sqrt[a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]],x_Symbol] :=
  Sqrt[Pi]*(f+g*x)^(m+1)/(b*g*n*Rt[(m+1)/(b*n),2]*E^(a*(m+1)/(b*n))*(c*(d+e*x)^n)^((m+1)/n))*
    Erfi[Rt[(m+1)/(b*n),2]*Sqrt[a+b*Log[c*(d+e*x)^n]]] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f-d*g] && NonzeroQ[m+1] && PosQ[(m+1)/(b*n)]


Int[(f_.+g_.*x_)^m_./Sqrt[a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]],x_Symbol] :=
  Sqrt[Pi]*(f+g*x)^(m+1)/(b*g*n*Rt[-(m+1)/(b*n),2]*E^(a*(m+1)/(b*n))*(c*(d+e*x)^n)^((m+1)/n))*
    Erf[Rt[-(m+1)/(b*n),2]*Sqrt[a+b*Log[c*(d+e*x)^n]]] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f-d*g] && NonzeroQ[m+1] && NegQ[(m+1)/(b*n)]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
  (f+g*x)^(m+1)*(a+b*Log[c*(d+e*x)^n])^(p+1)/(b*g*n*(p+1)) - 
  (m+1)/(b*n*(p+1))*Int[(f+g*x)^m*(a+b*Log[c*(d+e*x)^n])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && ZeroQ[e*f-d*g] && NonzeroQ[m+1] && RationalQ[p] && p<-1


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_.,x_Symbol] :=
  (f+g*x)^(m+1)*(a+b*Log[c*(d+e*x)^n])^p/
    (g*(m+1)*E^(a*(m+1)/(b*n))*(c*(d+e*x)^n)^((m+1)/n)*(-(m+1)*(a+b*Log[c*(d+e*x)^n])/(b*n))^p)*
    Gamma[p+1,-(m+1)*(a+b*Log[c*(d+e*x)^n])/(b*n)] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[e*f-d*g] && NonzeroQ[m+1]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]),x_Symbol] :=
  (f+g*x)^(m+1)*(a+b*Log[c*(d+e*x)^n])/(g*(m+1)) - 
  b*e*n/(g*(m+1))*Int[(f+g*x)^(m+1)/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && NonzeroQ[m+1]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_.,x_Symbol] :=
  (d+e*x)*(f+g*x)^m*(a+b*Log[c*(d+e*x)^n])^p/(e*(m+1)) + 
  m*(e*f-d*g)/(e*(m+1))*Int[(f+g*x)^(m-1)*(a+b*Log[c*(d+e*x)^n])^p,x] - 
  b*n*p/(m+1)*Int[(f+g*x)^m*(a+b*Log[c*(d+e*x)^n])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && RationalQ[m,p] && p>0 && m>0


Int[Log[c_.*(d_.+e_.*x_)]/(f_.+g_.*x_),x_Symbol] :=
  -1/g*PolyLog[2,-Together[c*e/g]*(f+g*x)] /;
FreeQ[{c,d,e,f,g},x] && ZeroQ[g+c*(e*f-d*g)]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_./(f_.+g_.*x_),x_Symbol] :=
  1/g*(a+b*Log[c*(d+e*x)^n])^p*Log[e*(f+g*x)/(e*f-d*g)] - 
  b*e*n*p/g*Int[(a+b*Log[c*(d+e*x)^n])^(p-1)*Log[(e*(f+g*x))/(e*f-d*g)]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && RationalQ[p] && p>0


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_./(f_.+g_.*x_)^2,x_Symbol] :=
  (d+e*x)*(a+b*Log[c*(d+e*x)^n])^p/((e*f-d*g)*(f+g*x)) - 
  b*e*n*p/(e*f-d*g)*Int[(a+b*Log[c*(d+e*x)^n])^(p-1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && RationalQ[p] && p>0


Int[(f_.+g_.*x_)^m_*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_.,x_Symbol] :=
  -(d+e*x)*(f+g*x)^(m+1)*(a+b*Log[c*(d+e*x)^n])^p/((e*f-d*g)*(m+1)) + 
  e*(m+2)/((e*f-d*g)*(m+1))*Int[(f+g*x)^(m+1)*(a+b*Log[c*(d+e*x)^n])^p,x] + 
  b*e*n*p/((e*f-d*g)*(m+1))*Int[(f+g*x)^(m+1)*(a+b*Log[c*(d+e*x)^n])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && RationalQ[m,p] && p>0 && m<-1 && m!=-2


Int[(f_.+g_.*x_)^m_./(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]),x_Symbol] :=
  Int[ExpandIntegrand[(f+g*x)^m/(a+b*Log[c*(d+e*x)^n]),x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && PositiveIntegerQ[m]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
  (d+e*x)*(f+g*x)^m*(a+b*Log[c*(d+e*x)^n])^(p+1)/(b*e*n*(p+1)) + 
  m*(e*f-d*g)/(b*e*n*(p+1))*Int[(f+g*x)^(m-1)*(a+b*Log[c*(d+e*x)^n])^(p+1),x] - 
  (m+1)/(b*n*(p+1))*Int[(f+g*x)^m*(a+b*Log[c*(d+e*x)^n])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && RationalQ[m,p] && p<-1 && m>0


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
  Int[ExpandIntegrand[(f+g*x)^m*(a+b*Log[c*(d+e*x)^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NonzeroQ[e*f-d*g] && PositiveIntegerQ[m]


Int[u_^m_.*(a_.+b_.*Log[c_.*v_^n_.])^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Log[c*ExpandToSum[v,x]^n])^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[x_^q1_.*(f_.+g_.*x_^q_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_^q_)^n_.])^p_.,x_Symbol] :=
  1/q*Subst[Int[(f+g*x)^m*(a+b*Log[c*(d+e*x)^n])^p,x],x,x^q] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q},x] && ZeroQ[q1-(q-1)]


Int[Log[j_.*(h_.+i_.*x_)]/(f_.+g_.*x_)*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_.,x_Symbol] :=
  -PolyLog[2,Together[1-j*(h+i*x)]]/g*(a+b*Log[c*(d+e*x)^n])^p + 
  b*e*n*p/g*Int[PolyLog[2,Together[1-j*(h+i*x)]]/(d+e*x)*(a+b*Log[c*(d+e*x)^n])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,n},x] && RationalQ[p] && p>0 && ZeroQ[g-j*(g*h-f*i)]


Int[Log[1+j_.*(h_.+i_.*x_)^m_.]/(f_.+g_.*x_)*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_.,x_Symbol] :=
  -PolyLog[2,-j*(h+i*x)^m]/(g*m)*(a+b*Log[c*(d+e*x)^n])^p + 
  b*e*n*p/(g*m)*Int[PolyLog[2,-j*(h+i*x)^m]/(d+e*x)*(a+b*Log[c*(d+e*x)^n])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && RationalQ[p] && p>0 && ZeroQ[g*h-f*i]


Int[PolyLog[q_,j_.*(h_.+i_.*x_)^m_.]/(f_.+g_.*x_)*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_.,x_Symbol] :=
  PolyLog[q+1,j*(h+i*x)^m]/(g*m)*(a+b*Log[c*(d+e*x)^n])^p - 
  b*e*n*p/(g*m)*Int[PolyLog[q+1,j*(h+i*x)^m]/(d+e*x)*(a+b*Log[c*(d+e*x)^n])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n,q},x] && RationalQ[p] && p>0 && ZeroQ[g*h-f*i]


Int[u_.*(a_.+b_.*Log[c_.*v_^n_.])^p_.,x_Symbol] :=
  Int[u*(a+b*Log[c*ExpandToSum[v,x]^n])^p,x] /;
FreeQ[{a,b,c,n,p},x] && LinearQ[v,x] && Not[LinearMatchQ[v,x]]


Int[Log[c_.*(a_.+b_.*x_^n_)^p_.],x_Symbol] :=
  x*Log[c*(a+b*x^n)^p] -
  b*n*p*Int[x^n/(a+b*x^n),x] /;
FreeQ[{a,b,c,n,p},x]


Int[Log[c_.*(a_+b_.*x_^n_.)]/x_,x_Symbol] :=
  -PolyLog[2,-b*c*x^n]/n /;
FreeQ[{a,b,c,n},x] && ZeroQ[a*c-1]


Int[Log[c_.*(a_+b_.*x_^n_.)]/x_,x_Symbol] :=
  Log[a*c]*Log[x] +
  Int[Log[1+b*x^n/a]/x,x] /;
FreeQ[{a,b,c,n},x] && PositiveQ[a*c] && NonzeroQ[a*c-1]


Int[Log[c_.*(a_+b_.*x_^n_.)^p_.]/x_,x_Symbol] :=
  Log[c*(a+b*x^n)^p]*Log[-b*x^n/a]/n -
  b*p*Int[x^(n-1)*Log[-b*x^n/a]/(a+b*x^n),x] /;
FreeQ[{a,b,c,n,p},x] && Not[PositiveQ[a*c]]


Int[x_^m_.*Log[c_.*(a_.+b_.*x_^n_)^p_.],x_Symbol] :=
  1/n*Subst[Int[Log[c*(a+b*x)^p],x],x,x^n] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[m-(n-1)]


Int[Log[c_.*(a_.+b_.*x_^n_)^p_.]/(d_.+e_.*x_),x_Symbol] :=
  Log[d+e*x]*Log[c*(a+b*x^n)^p]/e - 
  b*n*p/e*Int[x^(n-1)*Log[d+e*x]/(a+b*x^n),x] /;
FreeQ[{a,b,c,d,e,p},x]


Int[(d_.+e_.*x_)^m_.*Log[c_.*(a_.+b_.*x_^n_)^p_.],x_Symbol] :=
  (d+e*x)^(m+1)*Log[c*(a+b*x^n)^p]/(e*(m+1)) - 
  b*n*p/(e*(m+1))*Int[x^(n-1)*(d+e*x)^(m+1)/(a+b*x^n),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NonzeroQ[m+1]


Int[u_.*Log[c_.*v_^p_.],x_Symbol] :=
  Int[u*Log[c*ExpandToSum[v,x]^p],x] /;
FreeQ[{c,p},x] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[Log[c_.*(a_+b_.*x_^2)^n_.]^p_,x_Symbol] :=
  x*Log[c*(a+b*x^2)^n]^p - 
  2*b*n*p*Int[x^2*Log[c*(a+b*x^2)^n]^(p-1)/(a+b*x^2),x] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*Log[c_.*(a_+b_.*x_^2)^n_.]^p_,x_Symbol] :=
  x^(m+1)*Log[c*(a+b*x^2)^n]^p/(m+1) - 
  2*b*n*p/(m+1)*Int[x^(m+2)*Log[c*(a+b*x^2)^n]^(p-1)/(a+b*x^2),x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p] && Not[IntegerQ[(m-1)/2]]


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


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  d/g*Int[1/(c+d*x)^2*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && ZeroQ[d*f-c*g]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  b/(g*n*n1*(b*c-a*d))*Subst[Int[x^p,x],x,Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[d*f-c*g] && ZeroQ[b*f-a*g]


Int[Log[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]/((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  1/(d*f-c*g)*PolyLog[2,Together[c-a*e]*(f+g*x)/(f*(c+d*x))] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b*c-a*d] && NonzeroQ[d*f-c*g] && NonzeroQ[b*f-a*g] && ZeroQ[d*f-c*g-e*(b*f-a*g)]


Int[Log[e_.*(e1_.*(a_.+b_.*x_)^n1_.*(c_.+d_.*x_)^n2_)^n_.]^p_./((c_.+d_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  -1/(d*f-c*g)*Log[(b*c-a*d)*(f+g*x)/((b*f-a*g)*(c+d*x))]*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^p + 
  n*n1*p*(b*c-a*d)/(d*f-c*g)*
    Int[(1/((a+b*x)*(c+d*x)))*Log[(b*c-a*d)*(f+g*x)/((b*f-a*g)*(c+d*x))]*Log[e*(e1*(a+b*x)^n1/(c+d*x)^n1)^n]^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n,e1,n1},x] && ZeroQ[n1+n2] && NonzeroQ[b*c-a*d] && NonzeroQ[d*f-c*g] && NonzeroQ[b*f-a*g] && PositiveIntegerQ[p]


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


Int[u_.*Log[v_]^p_.,x_Symbol] :=
  Module[{lst=QuotientOfLinearsParts[v,x]},
  Int[u*Log[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^p,x] /;
 Not[OneQ[p] && ZeroQ[lst[[3]]]]] /;
FreeQ[p,x] && QuotientOfLinearsQ[v,x] && Not[QuotientOfLinearsMatchQ[v,x]]


Int[u_*Log[v_],x_Symbol] :=
  Module[{w=DerivativeDivides[v,u*(1-v),x]},
  w*PolyLog[2,Together[1-v]] /;
 Not[FalseQ[w]]]


Int[u_*Log[w_]*Log[v_],x_Symbol] :=
  Module[{z=DerivativeDivides[v,u*(1-v),x]},
  z*Log[w]*PolyLog[2,Together[1-v]] - 
  Int[SimplifyIntegrand[z*D[w,x]*PolyLog[2,Together[1-v]]/w,x],x] /;
 Not[FalseQ[z]]] /;
InverseFunctionFreeQ[w,x]


Int[Log[c_.*Px_^n_.],x_Symbol] :=
  x*Log[c*Px^n] -
  n*Int[x*D[Px,x]/Px,x] /;
FreeQ[{c,n},x] && PolynomialQ[Px,x] && Exponent[Px,x]>1


Int[Log[c_.*Px_^n_.]/(a_.+b_.*x_),x_Symbol] :=
  Log[a+b*x]*Log[c*Px^n]/b - 
  n/b*Int[Log[a+b*x]*D[Px,x]/Px,x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x] && Exponent[Px,x]>1


Int[(a_.+b_.*x_)^m_.*Log[c_.*Px_^n_.],x_Symbol] :=
  (a+b*x)^(m+1)*Log[c*Px^n]/(b*(m+1)) -
  n/(b*(m+1))*Int[(a+b*x)^(m+1)*D[Px,x]/Px,x] /;
FreeQ[{a,b,c,m,n},x] && PolynomialQ[Px,x] && Exponent[Px,x]>1 && NonzeroQ[m+1]


(* Int[Log[c_.*Px_^n_.]/(a_.+b_.*x_^2),x_Symbol] :=
  1/(2*Rt[a,2])*Int[Log[c*Px^n]/(Rt[a,2]-Rt[-b,2]*x),x] + 
  1/(2*Rt[a,2])*Int[Log[c*Px^n]/(Rt[a,2]+Rt[-b,2]*x),x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x] && Exponent[Px,x]>1 && PosQ[a] *)


(* Int[Log[c_.*Px_^n_.]/(a_.+b_.*x_^2),x_Symbol] :=
  -1/(2*Rt[-a,2])*Int[Log[c*Px^n]/(Rt[-a,2]-Rt[b,2]*x),x] - 
  1/(2*Rt[-a,2])*Int[Log[c*Px^n]/(Rt[-a,2]+Rt[b,2]*x),x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x] && Exponent[Px,x]>1 && NegQ[a] *)


Int[Log[c_.*(b_.*(d_.+e_.*x_)^n_.)^p_.],x_Symbol] :=
  (d+e*x)*Log[c*(b*(d+e*x)^n)^p]/e - n*p*x /;
FreeQ[{b,c,d,e,n,p},x]


Int[Log[c_.*(a_+b_.*(d_.+e_.*x_)^n_)^p_.],x_Symbol] :=
  (d+e*x)*Log[c*(a+b*(d+e*x)^n)^p]/e -
  b*n*p*Int[1/(b+a*(d+e*x)^(-n)),x] /;
FreeQ[{a,b,c,d,e,p},x] && RationalQ[n] && n<0


Int[Log[c_.*(a_+b_.*(d_.+e_.*x_)^n_.)^p_.],x_Symbol] :=
  (d+e*x)*Log[c*(a+b*(d+e*x)^n)^p]/e - n*p*x +
  a*n*p*Int[1/(a+b*(d+e*x)^n),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[RationalQ[n] && n<0]


Int[(f_.+g_.*x_)^m_.*Log[1+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  -(f+g*x)^m*PolyLog[2,-e*(F^(c*(a+b*x)))^n]/(b*c*n*Log[F]) + 
  g*m/(b*c*n*Log[F])*Int[(f+g*x)^(m-1)*PolyLog[2,-e*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,e,f,g,n},x] && RationalQ[m] && m>0


Int[(f_.+g_.*x_)^m_.*Log[d_+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  (f+g*x)^(m+1)*Log[d+e*(F^(c*(a+b*x)))^n]/(g*(m+1)) - 
  (f+g*x)^(m+1)*Log[1+e/d*(F^(c*(a+b*x)))^n]/(g*(m+1)) + 
  Int[(f+g*x)^m*Log[1+e/d*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && RationalQ[m] && m>0 && NonzeroQ[d-1]


Int[ArcSin[d_.+e_.*x_]^m_.*Log[c_.*(a_.+b_.*x_^n_.)^p_.],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[ArcSin[d+e*x]^m,x]]},  
  Dist[Log[c*(a+b*x^n)^p],w,x] - 
  b*n*p*Int[SimplifyIntegrand[w*x^(n-1)/(a+b*x^n),x],x]] /;
FreeQ[{a,b,c,d,e,n,p},x] && PositiveIntegerQ[m]


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


Int[Log[d_.*(e_.+f_.*x_)^n_.]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[Log[d*(e+f*x)^n],1/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,n},x]


Int[Log[d_.*(e_+f_.*x_)^n_.]/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[Log[d*(e+f*x)^n],1/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,f,n},x]


Int[Log[u_]/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[1/(a+b*x+c*x^2),x]]},  
  w*Log[u] - Int[SimplifyIntegrand[w*D[u,x]/u,x],x]] /;
FreeQ[{a,b,c},x] && InverseFunctionFreeQ[u,x]


Int[Log[u_]/(a_+c_.*x_^2),x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[1/(a+c*x^2),x]]},  
  w*Log[u] - Int[SimplifyIntegrand[w*D[u,x]/u,x],x]] /;
FreeQ[{a,c},x] && InverseFunctionFreeQ[u,x]


Int[u_^(a_.*x_)*Log[u_],x_Symbol] :=
  u^(a*x)/a - Int[SimplifyIntegrand[x*u^(a*x-1)*D[u,x],x],x] /;
FreeQ[a,x] && InverseFunctionFreeQ[u,x]


Int[v_*Log[u_],x_Symbol] :=
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
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
  Module[{z=Block[{ShowSteps=False,StepCounter=Null}, Int[u,x]]},  
  Dist[Log[v]*Log[w],z,x] - 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/v,x],x] - 
  Int[SimplifyIntegrand[z*Log[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[Log[c_.*(a_+b_./x_)^n_.]^p_,x_Symbol] :=
  (b+a*x)*Log[c*(a+b/x)^n]^p/a + 
  b/a*n*p*Int[Log[c*(a+b/x)^n]^(p-1)/x,x] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[p]


Int[Log[d_.*(a_.+b_.*x_+c_.*x_^2)^n_.]^p_.,x_Symbol] :=
  Int[Log[d*(b+2*c*x)^(2*n)/(4^n*c^n)]^p,x] /;
FreeQ[{a,b,c,d,p},x] && IntegerQ[n] && ZeroQ[b^2-4*a*c]


Int[Log[d_.*(a_.+b_.*x_+c_.*x_^2)^n_.]^2,x_Symbol] :=
  x*Log[d*(a+b*x+c*x^2)^n]^2 -
  2*b*n*Int[x*Log[d*(a+b*x+c*x^2)^n]/(a+b*x+c*x^2),x] - 
  4*c*n*Int[x^2*Log[d*(a+b*x+c*x^2)^n]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,n},x] && Not[IntegerQ[n] && ZeroQ[b^2-4*a*c]]


Int[Log[a_.*(b_.*x_^n_.)^p_]^q_.,x_Symbol] :=
  Subst[Int[Log[x^(n*p)]^q,x],x^(n*p),a*(b*x^n)^p] /;
FreeQ[{a,b,n,p,q},x]


Int[x_^m_.*Log[a_.*(b_.*x_^n_.)^p_]^q_.,x_Symbol] :=
  Subst[Int[x^m*Log[x^(n*p)]^q,x],x^(n*p),a*(b*x^n)^p] /;
FreeQ[{a,b,m,n,p,q},x] && NonzeroQ[m+1] && Not[x^(n*p)===a*(b*x^n)^p]


Int[Log[a_.*(b_.*(c_.*x_^n_.)^p_)^q_]^r_.,x_Symbol] :=
  Subst[Int[Log[x^(n*p*q)]^r,x],x^(n*p*q),a*(b*(c*x^n)^p)^q] /;
FreeQ[{a,b,c,n,p,q,r},x]


Int[x_^m_.*Log[a_.*(b_.*(c_.*x_^n_.)^p_)^q_]^r_.,x_Symbol] :=
  Subst[Int[x^m*Log[x^(n*p*q)]^r,x],x^(n*p*q),a*(b*(c*x^n)^p)^q] /;
FreeQ[{a,b,c,m,n,p,q,r},x] && NonzeroQ[m+1] && Not[x^(n*p*q)===a*(b*(c*x^n)^p)^q]


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
