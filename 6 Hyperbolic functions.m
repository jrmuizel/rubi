(* ::Package:: *)

(* ::Section:: *)
(*Hyperbolic Function Rules*)


(* ::Subsection::Closed:: *)
(*6.1.10 (c+d x)^m (a+b sinh)^n*)


Int[u_^m_.*(a_.+b_.*Sinh[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Sinh[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*(a_.+b_.*Cosh[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Cosh[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]





(* ::Subsection::Closed:: *)
(*6.1.11 (e x)^m (a+b x^n)^p sinh*)


Int[(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sinh[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]


Int[(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cosh[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]


Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  x^(-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) - 
  (-n+1)/(b*n*(p+1))*Int[x^(-n)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && IGtQ[n,0] && LtQ[p,-1] && GtQ[n,2]


Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  x^(-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) - 
  (-n+1)/(b*n*(p+1))*Int[x^(-n)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && IGtQ[n,0] && LtQ[p,-1] && GtQ[n,2]


Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sinh[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])


Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cosh[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])


Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[x^(n*p)*(b+a*x^(-n))^p*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && ILtQ[n,0]


Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[x^(n*p)*(b+a*x^(-n))^p*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && ILtQ[n,0]


Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Unintegrable[(a+b*x^n)^p*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Unintegrable[(a+b*x^n)^p*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sinh[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cosh[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  e^m*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) - 
  d*e^m/(b*n*(p+1))*Int[(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && EqQ[m-n+1,0] && LtQ[p,-1] && (IntegerQ[n] || GtQ[e,0])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  e^m*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) - 
  d*e^m/(b*n*(p+1))*Int[(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && EqQ[m-n+1,0] && LtQ[p,-1] && (IntegerQ[n] || GtQ[e,0])


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  x^(m-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,-1] && IGtQ[n,0] && RationalQ[m] && (GtQ[m-n+1,0] || GtQ[n,2])


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  x^(m-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,-1] && IGtQ[n,0] && RationalQ[m] && (GtQ[m-n+1,0] || GtQ[n,2])


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sinh[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cosh[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
  Int[x^(m+n*p)*(b+a*x^(-n))^p*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,m},x] && ILtQ[p,0] && ILtQ[n,0]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
  Int[x^(m+n*p)*(b+a*x^(-n))^p*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,m},x] && ILtQ[p,0] && ILtQ[n,0]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
  Unintegrable[(e*x)^m*(a+b*x^n)^p*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
  Unintegrable[(e*x)^m*(a+b*x^n)^p*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]





(* ::Subsection::Closed:: *)
(*6.1.12 (e x)^m (a+b sinh(c+d x^n))^p*)


Int[Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(c+d*x^n),x] - 1/2*Int[E^(-c-d*x^n),x] /;
FreeQ[{c,d},x] && IGtQ[n,1]


Int[Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(c+d*x^n),x] + 1/2*Int[E^(-c-d*x^n),x] /;
FreeQ[{c,d},x] && IGtQ[n,1]


Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Sinh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[n,1] && IGtQ[p,1]


Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Cosh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[n,1] && IGtQ[p,1]


Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d},x] && ILtQ[n,0] && IntegerQ[p]


Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d},x] && ILtQ[n,0] && IntegerQ[p]


Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*Sinh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d},x] && FractionQ[n] && IntegerQ[p]


Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*Cosh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d},x] && FractionQ[n] && IntegerQ[p]


Int[Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(c+d*x^n),x] - 1/2*Int[E^(-c-d*x^n),x] /;
FreeQ[{c,d,n},x]


Int[Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(c+d*x^n),x] + 1/2*Int[E^(-c-d*x^n),x] /;
FreeQ[{c,d,n},x]


Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Sinh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]


Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Cosh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]


Int[(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Sinh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[p] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Cosh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[p] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_,x_Symbol] :=
  Unintegrable[(a+b*Sinh[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x]


Int[(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_,x_Symbol] :=
  Unintegrable[(a+b*Cosh[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x]


Int[(a_.+b_.*Sinh[u_])^p_.,x_Symbol] :=
  Int[(a+b*Sinh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*Cosh[u_])^p_.,x_Symbol] :=
  Int[(a+b*Cosh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[Sinh[d_.*x_^n_]/x_,x_Symbol] :=
  SinhIntegral[d*x^n]/n /;
FreeQ[{d,n},x]


Int[Cosh[d_.*x_^n_]/x_,x_Symbol] :=
  CoshIntegral[d*x^n]/n /;
FreeQ[{d,n},x]


Int[Sinh[c_+d_.*x_^n_]/x_,x_Symbol] :=
  Sinh[c]*Int[Cosh[d*x^n]/x,x] + Cosh[c]*Int[Sinh[d*x^n]/x,x] /;
FreeQ[{c,d,n},x]


Int[Cosh[c_+d_.*x_^n_]/x_,x_Symbol] :=
  Cosh[c]*Int[Cosh[d*x^n]/x,x] + Sinh[c]*Int[Sinh[d*x^n]/x,x] /;
FreeQ[{c,d,n},x]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Sinh[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]] && (EqQ[p,1] || EqQ[m,n-1] || IntegerQ[p] && GtQ[Simplify[(m+1)/n],0])


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Cosh[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]] && (EqQ[p,1] || EqQ[m,n-1] || IntegerQ[p] && GtQ[Simplify[(m+1)/n],0])


Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*Cosh[c+d*x^n]/(d*n) - 
  e^n*(m-n+1)/(d*n)*Int[(e*x)^(m-n)*Cosh[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[0,n,m+1]


Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*Sinh[c+d*x^n]/(d*n) - 
  e^n*(m-n+1)/(d*n)*Int[(e*x)^(m-n)*Sinh[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[0,n,m+1]


Int[(e_.*x_)^m_*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  (e*x)^(m+1)*Sinh[c+d*x^n]/(e*(m+1)) - 
  d*n/(e^n*(m+1))*Int[(e*x)^(m+n)*Cosh[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[m,-1]


Int[(e_.*x_)^m_*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  (e*x)^(m+1)*Cosh[c+d*x^n]/(e*(m+1)) - 
  d*n/(e^n*(m+1))*Int[(e*x)^(m+n)*Sinh[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[m,-1]


Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(c+d*x^n),x] - 1/2*Int[(e*x)^m*E^(-c-d*x^n),x] /;
FreeQ[{c,d,e,m},x] && IGtQ[n,0]


Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(c+d*x^n),x] + 1/2*Int[(e*x)^m*E^(-c-d*x^n),x] /;
FreeQ[{c,d,e,m},x] && IGtQ[n,0]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -Sinh[a+b*x^n]^p/((n-1)*x^(n-1)) + 
  b*n*p/(n-1)*Int[Sinh[a+b*x^n]^(p-1)*Cosh[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && EqQ[m+n,0] && GtQ[p,1] && NeQ[n,1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -Cosh[a+b*x^n]^p/((n-1)*x^(n-1)) + 
  b*n*p/(n-1)*Int[Cosh[a+b*x^n]^(p-1)*Sinh[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && EqQ[m+n,0] && GtQ[p,1] && NeQ[n,1]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -n*Sinh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^n*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/(b*n*p) -
  (p-1)/p*Int[x^m*Sinh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1] && GtQ[p,1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -n*Cosh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^n*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Cosh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1] && GtQ[p,1]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -(m-n+1)*x^(m-2*n+1)*Sinh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^(m-n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/(b*n*p) -
  (p-1)/p*Int[x^m*Sinh[a+b*x^n]^(p-2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2)*Int[x^(m-2*n)*Sinh[a+b*x^n]^p,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && GtQ[p,1] && LtQ[0,2*n,m+1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -(m-n+1)*x^(m-2*n+1)*Cosh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^(m-n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Cosh[a+b*x^n]^(p-2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2)*Int[x^(m-2*n)*Cosh[a+b*x^n]^p,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && GtQ[p,1] && LtQ[0,2*n,m+1]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m+1)*Sinh[a+b*x^n]^p/(m+1) - 
  b*n*p*x^(m+n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) + 
  b^2*n^2*p^2/((m+1)*(m+n+1))*Int[x^(m+2*n)*Sinh[a+b*x^n]^p,x] + 
  b^2*n^2*p*(p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*Sinh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && GtQ[p,1] && LtQ[0,2*n,1-m] && NeQ[m+n+1,0]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m+1)*Cosh[a+b*x^n]^p/(m+1) - 
  b*n*p*x^(m+n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) + 
  b^2*n^2*p^2/((m+1)*(m+n+1))*Int[x^(m+2*n)*Cosh[a+b*x^n]^p,x] - 
  b^2*n^2*p*(p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*Cosh[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && GtQ[p,1] && LtQ[0,2*n,1-m] && NeQ[m+n+1,0]


Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  k/e*Subst[Int[x^(k*(m+1)-1)*(a+b*Sinh[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && IGtQ[n,0] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  k/e*Subst[Int[x^(k*(m+1)-1)*(a+b*Cosh[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && IGtQ[n,0] && FractionQ[m]


Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Sinh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,1] && IGtQ[n,0]


Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Cosh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,1] && IGtQ[n,0]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^n*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  n*Sinh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) - 
  (p+2)/(p+1)*Int[x^m*Sinh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1,0] && LtQ[p,-1] && NeQ[p,-2]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^n*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) + 
  n*Cosh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) + 
  (p+2)/(p+1)*Int[x^m*Cosh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1,0] && LtQ[p,-1] && NeQ[p,-2]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m-n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)*x^(m-2*n+1)*Sinh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) -
  (p+2)/(p+1)*Int[x^m*Sinh[a+b*x^n]^(p+2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2))*Int[x^(m-2*n)*Sinh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && LtQ[p,-1] && NeQ[p,-2] && LtQ[0,2*n,m+1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^(m-n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) +
  (m-n+1)*x^(m-2*n+1)*Cosh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (p+2)/(p+1)*Int[x^m*Cosh[a+b*x^n]^(p+2),x] -
  (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2))*Int[x^(m-2*n)*Cosh[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && LtQ[p,-1] && NeQ[p,-2] && LtQ[0,2*n,m+1]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ILtQ[n,0] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ILtQ[n,0] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/e*Subst[Int[(a+b*Sinh[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && ILtQ[n,0] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/e*Subst[Int[(a+b*Cosh[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && ILtQ[n,0] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && ILtQ[n,0] && Not[RationalQ[m]]


Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && ILtQ[n,0] && Not[RationalQ[m]]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*Sinh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*Cosh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]


Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]


Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*Sinh[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*Cosh[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]


Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]


Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]


Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(c+d*x^n),x] - 1/2*Int[(e*x)^m*E^(-c-d*x^n),x] /;
FreeQ[{c,d,e,m,n},x]


Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(c+d*x^n),x] + 1/2*Int[(e*x)^m*E^(-c-d*x^n),x] /;
FreeQ[{c,d,e,m,n},x]


Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Sinh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]


Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Cosh[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]


Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*(a+b*Sinh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*(a+b*Cosh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x] && IntegerQ[m]


Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  Unintegrable[(e*x)^m*(a+b*Sinh[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && LinearQ[u,x]


Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  Unintegrable[(e*x)^m*(a+b*Cosh[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && LinearQ[u,x]


Int[(e_*x_)^m_.*(a_.+b_.*Sinh[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Sinh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(e_*x_)^m_.*(a_.+b_.*Cosh[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Cosh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
  Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && EqQ[m,n-1] && NeQ[p,-1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
  Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && EqQ[m,n-1] && NeQ[p,-1]


Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
  x^(m-n+1)*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Sinh[a+b*x^n]^(p+1),x] /;
FreeQ[{a,b,p},x] && LtQ[0,n,m+1] && NeQ[p,-1]


Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
  x^(m-n+1)*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Cosh[a+b*x^n]^(p+1),x] /;
FreeQ[{a,b,p},x] && LtQ[0,n,m+1] && NeQ[p,-1]





(* ::Subsection::Closed:: *)
(*6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n*)
(**)


Int[Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  1/2*Int[E^(a+b*x+c*x^2),x] - 1/2*Int[E^(-a-b*x-c*x^2),x] /;
FreeQ[{a,b,c},x]


Int[Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  1/2*Int[E^(a+b*x+c*x^2),x] + 1/2*Int[E^(-a-b*x-c*x^2),x] /;
FreeQ[{a,b,c},x]


Int[Sinh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[Sinh[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c},x] && IGtQ[n,1]


Int[Cosh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[Cosh[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c},x] && IGtQ[n,1]


Int[Sinh[v_]^n_.,x_Symbol] :=
  Int[Sinh[ExpandToSum[v,x]]^n,x] /;
IGtQ[n,0] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[Cosh[v_]^n_.,x_Symbol] :=
  Int[Cosh[ExpandToSum[v,x]]^n,x] /;
IGtQ[n,0] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[(d_.+e_.*x_)*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Cosh[a+b*x+c*x^2]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && EqQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Sinh[a+b*x+c*x^2]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && EqQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Cosh[a+b*x+c*x^2]/(2*c) -
  (b*e-2*c*d)/(2*c)*Int[Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Sinh[a+b*x+c*x^2]/(2*c) - 
  (b*e-2*c*d)/(2*c)*Int[Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2]/(2*c) -
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && GtQ[m,1] && EqQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2]/(2*c) - 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && GtQ[m,1] && EqQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2]/(2*c) -
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2],x] -
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && GtQ[m,1] && NeQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2]/(2*c) - 
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2],x] - 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && GtQ[m,1] && NeQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sinh[a+b*x+c*x^2]/(e*(m+1)) -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && LtQ[m,-1] && EqQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Cosh[a+b*x+c*x^2]/(e*(m+1)) - 
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && LtQ[m,-1] && EqQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sinh[a+b*x+c*x^2]/(e*(m+1)) -
  (b*e-2*c*d)/(e^2*(m+1))*Int[(d+e*x)^(m+1)*Cosh[a+b*x+c*x^2],x] -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && LtQ[m,-1] && NeQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Cosh[a+b*x+c*x^2]/(e*(m+1)) - 
  (b*e-2*c*d)/(e^2*(m+1))*Int[(d+e*x)^(m+1)*Sinh[a+b*x+c*x^2],x] -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && LtQ[m,-1] && NeQ[b*e-2*c*d,0]


Int[(d_.+e_.*x_)^m_.*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Unintegrable[(d+e*x)^m*Sinh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x]


Int[(d_.+e_.*x_)^m_.*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Unintegrable[(d+e*x)^m*Cosh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x]


Int[(d_.+e_.*x_)^m_.*Sinh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(d+e*x)^m,Sinh[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1]


Int[(d_.+e_.*x_)^m_.*Cosh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(d+e*x)^m,Cosh[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1]


Int[u_^m_.*Sinh[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Sinh[ExpandToSum[v,x]]^n,x] /;
FreeQ[m,x] && IGtQ[n,0] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[u_^m_.*Cosh[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Cosh[ExpandToSum[v,x]]^n,x] /;
FreeQ[m,x] && IGtQ[n,0] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]





(* ::Subsection::Closed:: *)
(*6.2.10 (c+d x)^m (a+b tanh)^n*)


Int[u_^m_.*(a_.+b_.*Tanh[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Tanh[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*(a_.+b_.*Coth[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Coth[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]





(* ::Subsection::Closed:: *)
(*6.2.11 (e x)^m (a+b tanh(c+d x^n))^p*)


Int[(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Tanh[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && IGtQ[1/n,0] && IntegerQ[p]


Int[(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Coth[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && IGtQ[1/n,0] && IntegerQ[p]


Int[(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Integral[(a+b*Tanh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Integral[(a+b*Coth[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Tanh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Tanh[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+b_.*Coth[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Coth[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+b_.*Tanh[u_])^p_.,x_Symbol] :=
  Int[(a+b*Tanh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*Coth[u_])^p_.,x_Symbol] :=
  Int[(a+b*Coth[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Tanh[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && IGtQ[Simplify[(m+1)/n],0] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Coth[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && IGtQ[Simplify[(m+1)/n],0] && IntegerQ[p]


Int[x_^m_.*Tanh[c_.+d_.*x_^n_]^2,x_Symbol] :=
  -x^(m-n+1)*Tanh[c+d*x^n]/(d*n) + Int[x^m,x] + (m-n+1)/(d*n)*Int[x^(m-n)*Tanh[c+d*x^n],x] /;
FreeQ[{c,d,m,n},x]


Int[x_^m_.*Coth[c_.+d_.*x_^n_]^2,x_Symbol] :=
  -x^(m-n+1)*Coth[c+d*x^n]/(d*n) + Int[x^m,x] + (m-n+1)/(d*n)*Int[x^(m-n)*Coth[c+d*x^n],x] /;
FreeQ[{c,d,m,n},x]


Int[x_^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Integral[x^m*(a+b*Tanh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[x_^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Integral[x^m*(a+b*Coth[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Tanh[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Coth[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Tanh[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Tanh[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(e_*x_)^m_.*(a_.+b_.*Coth[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Coth[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_.*Tanh[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
  -x^(m-n+1)*Sech[a+b*x^n]^p/(b*n*p) +
  (m-n+1)/(b*n*p)*Int[x^(m-n)*Sech[a+b*x^n]^p,x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && GeQ[m-n,0] && EqQ[q,1]


Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_.*Coth[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
  -x^(m-n+1)*Csch[a+b*x^n]^p/(b*n*p) +
  (m-n+1)/(b*n*p)*Int[x^(m-n)*Csch[a+b*x^n]^p,x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && GeQ[m-n,0] && EqQ[q,1]





(* ::Subsection::Closed:: *)
(*6.2.12 (d+e x)^m tanh(a+b x+c x^2)^n*)
(**)


Int[Tanh[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Integral[Tanh[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,n},x]


Int[Coth[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Integral[Coth[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,n},x]


Int[(d_.+e_.*x_)*Tanh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Log[Cosh[a+b*x+c*x^2]]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Tanh[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)*Coth[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Log[Sinh[a+b*x+c*x^2]]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Coth[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x]


(* Int[x_^m_*Tanh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  x^(m-1)*Log[Cosh[a+b*x+c*x^2]]/(2*c) -
  b/(2*c)*Int[x^(m-1)*Tanh[a+b*x+c*x^2],x] -
  (m-1)/(2*c)*Int[x^(m-2)*Log[Cosh[a+b*x+c*x^2]],x] /;
FreeQ[{a,b,c},x] && GtQ[m,1] *)


(* Int[x_^m_*Coth[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  x^(m-1)*Log[Sinh[a+b*x+c*x^2]]/(2*c) -
  b/(2*c)*Int[x^(m-1)*Coth[a+b*x+c*x^2],x] -
  (m-1)/(2*c)*Int[x^(m-2)*Log[Sinh[a+b*x+c*x^2]],x] /;
FreeQ[{a,b,c},x] && GtQ[m,1] *)


Int[(d_.+e_.*x_)^m_.*Tanh[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Integral[(d+e*x)^m*Tanh[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(d_.+e_.*x_)^m_.*Coth[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Integral[(d+e*x)^m*Coth[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]





(* ::Subsection::Closed:: *)
(*6.3.10 (c+d x)^m (a+b sech)^n*)


Int[u_^m_.*Sech[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Sech[ExpandToSum[v,x]]^n,x] /;
FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*Csch[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Csch[ExpandToSum[v,x]]^n,x] /;
FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]





(* ::Subsection::Closed:: *)
(*6.3.11 (e x)^m (a+b sech(c+d x^n))^p*)
(**)


Int[(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Sech[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && IGtQ[1/n,0] && IntegerQ[p]


Int[(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Csch[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && IGtQ[1/n,0] && IntegerQ[p]


Int[(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Unintegrable[(a+b*Sech[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Unintegrable[(a+b*Csch[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Sech[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Sech[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+b_.*Csch[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Csch[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+b_.*Sech[u_])^p_.,x_Symbol] :=
  Int[(a+b*Sech[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*Csch[u_])^p_.,x_Symbol] :=
  Int[(a+b*Csch[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Sech[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && IGtQ[Simplify[(m+1)/n],0] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Csch[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && IGtQ[Simplify[(m+1)/n],0] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Unintegrable[x^m*(a+b*Sech[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[x_^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Unintegrable[x^m*(a+b*Csch[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sech[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Csch[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Sech[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Sech[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(e_*x_)^m_.*(a_.+b_.*Csch[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Csch[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Sech[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Sech[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && IntegerQ[n] && GeQ[m-n,0] && NeQ[p,1]


Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Csch[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Csch[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && IntegerQ[n] && GeQ[m-n,0] && NeQ[p,1]





(* ::Subsection::Closed:: *)
(*6.4.5 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p*)


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Cosh[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*Sinh[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Sinh[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]*Cosh[a_.+b_.*x_]^n_.,x_Symbol] :=
  (c+d*x)^m*Cosh[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Cosh[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Cosh[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Sinh[a+b*x]^n*Cosh[a+b*x]^p,x],x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]


Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[(c+d*x)^m*Sinh[a+b*x]^n*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sinh[a+b*x]^(n-2)*Tanh[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]


Int[(c_.+d_.*x_)^m_.*Cosh[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[(c+d*x)^m*Cosh[a+b*x]^n*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Cosh[a+b*x]^(n-2)*Coth[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
  -(c+d*x)^m*Sech[a+b*x]^n/(b*n) + 
  d*m/(b*n)*Int[(c+d*x)^(m-1)*Sech[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && EqQ[p,1] && GtQ[m,0]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
  -(c+d*x)^m*Csch[a+b*x]^n/(b*n) + 
  d*m/(b*n)*Int[(c+d*x)^(m-1)*Csch[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && EqQ[p,1] && GtQ[m,0]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^2*Tanh[a_.+b_.*x_]^n_.,x_Symbol] :=
  (c+d*x)^m*Tanh[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Tanh[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^2*Coth[a_.+b_.*x_]^n_.,x_Symbol] :=
  -(c+d*x)^m*Coth[a+b*x]^(n+1)/(b*(n+1)) + 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Coth[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]*Tanh[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[(c+d*x)^m*Sech[a+b*x]*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sech[a+b*x]^3*Tanh[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[p/2,0]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[(c+d*x)^m*Sech[a+b*x]^n*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sech[a+b*x]^(n+2)*Tanh[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && IGtQ[p/2,0]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]*Coth[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[(c+d*x)^m*Csch[a+b*x]*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csch[a+b*x]^3*Coth[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[p/2,0]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_,x_Symbol] :=
  Int[(c+d*x)^m*Csch[a+b*x]^n*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csch[a+b*x]^(n+2)*Coth[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && IGtQ[p/2,0]


Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
  With[{u=IntHide[Sech[a+b*x]^n*Tanh[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d,n,p},x] && IGtQ[m,0] && (IntegerQ[n/2] || IntegerQ[(p-1)/2])


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
  With[{u=IntHide[Csch[a+b*x]^n*Coth[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d,n,p},x] && IGtQ[m,0] && (IntegerQ[n/2] || IntegerQ[(p-1)/2])


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Sech[a_.+b_.*x_]^n_., x_Symbol] :=
  2^n*Int[(c+d*x)^m*Csch[2*a+2*b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && IntegerQ[n]


Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Sech[a_.+b_.*x_]^p_., x_Symbol] :=
  With[{u=IntHide[Csch[a+b*x]^n*Sech[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && GtQ[m,0] && NeQ[n,p]


Int[u_^m_.*F_[v_]^n_.*G_[w_]^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F[ExpandToSum[v,x]]^n*G[ExpandToSum[v,x]]^p,x] /;
FreeQ[{m,n,p},x] && HyperbolicQ[F] && HyperbolicQ[G] && EqQ[v,w] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]*(a_+b_.*Sinh[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Sinh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Sinh[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]*(a_+b_.*Cosh[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Cosh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Cosh[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^2*(a_+b_.*Tanh[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Tanh[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Tanh[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^2*(a_+b_.*Coth[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Coth[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Coth[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]*Tanh[c_.+d_.*x_]*(a_+b_.*Sech[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Sech[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Sech[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]*Coth[c_.+d_.*x_]*(a_+b_.*Csch[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Csch[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Csch[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]


Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]^p_.*Sinh[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Sinh[a+b*x]^p*Sinh[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IGtQ[q,0] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Cosh[a+b*x]^p*Cosh[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IGtQ[q,0] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Sinh[a+b*x]^p*Cosh[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0] && IGtQ[q,0]


Int[(e_.+f_.*x_)^m_.*F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigExpand[(e+f*x)^m*G[c+d*x]^q,F,c+d*x,p,b/d,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && MemberQ[{Sinh,Cosh},F] && MemberQ[{Sech,Csch},G] && IGtQ[p,0] && IGtQ[q,0] && EqQ[b*c-a*d,0] && IGtQ[b/d,1]





(* ::Subsection::Closed:: *)
(*6.4.6 F^(c (a+b x)) hyper(d+e x)^n*)


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_],x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) + 
  e*F^(c*(a+b*x))*Cosh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2-b^2*c^2*Log[F]^2,0]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_],x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) + 
  e*F^(c*(a+b*x))*Sinh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2-b^2*c^2*Log[F]^2,0]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2) + 
  e*n*F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n-1)/(e^2*n^2-b^2*c^2*Log[F]^2) - 
  n*(n-1)*e^2/(e^2*n^2-b^2*c^2*Log[F]^2)*Int[F^(c*(a+b*x))*Sinh[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2-b^2*c^2*Log[F]^2,0] && GtQ[n,1]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2) + 
  e*n*F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n-1)/(e^2*n^2-b^2*c^2*Log[F]^2) + 
  n*(n-1)*e^2/(e^2*n^2-b^2*c^2*Log[F]^2)*Int[F^(c*(a+b*x))*Cosh[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2-b^2*c^2*Log[F]^2,0] && GtQ[n,1]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) + 
  F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n+1)/(e*(n+1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2,0] && NeQ[n,-1] && NeQ[n,-2]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) - 
  F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n+1)/(e*(n+1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2,0] && NeQ[n,-1] && NeQ[n,-2]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) + 
  F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n+1)/(e*(n+1)) - 
  (e^2*(n+2)^2-b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2))*Int[F^(c*(a+b*x))*Sinh[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2,0] && LtQ[n,-1] && NeQ[n,-2]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) - 
  F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n+1)/(e*(n+1)) + 
  (e^2*(n+2)^2-b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2))*Int[F^(c*(a+b*x))*Cosh[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2,0] && LtQ[n,-1] && NeQ[n,-2]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
  E^(n*(d+e*x))*Sinh[d+e*x]^n/(-1+E^(2*(d+e*x)))^n*Int[F^(c*(a+b*x))*(-1+E^(2*(d+e*x)))^n/E^(n*(d+e*x)),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
  E^(n*(d+e*x))*Cosh[d+e*x]^n/(1+E^(2*(d+e*x)))^n*Int[F^(c*(a+b*x))*(1+E^(2*(d+e*x)))^n/E^(n*(d+e*x)),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Tanh[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandIntegrand[F^(c*(a+b*x))*(-1+E^(2*(d+e*x)))^n/(1+E^(2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Coth[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandIntegrand[F^(c*(a+b*x))*(1+E^(2*(d+e*x)))^n/(-1+E^(2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*(Sech[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2)) - 
  e*n*F^(c*(a+b*x))*Sech[d+e*x]^(n+1)*(Sinh[d+e*x]/(e^2*n^2-b^2*c^2*Log[F]^2)) + 
  e^2*n*((n+1)/(e^2*n^2-b^2*c^2*Log[F]^2))*Int[F^(c*(a+b*x))*Sech[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2,0] && LtQ[n,-1]


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*(Csch[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2)) - 
  e*n*F^(c*(a+b*x))*Csch[d+e*x]^(n+1)*(Cosh[d+e*x]/(e^2*n^2-b^2*c^2*Log[F]^2)) - 
  e^2*n*((n+1)/(e^2*n^2-b^2*c^2*Log[F]^2))*Int[F^(c*(a+b*x))*Csch[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2,0] && LtQ[n,-1]


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Sech[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Sech[d+e*x]^(n-1)*Sinh[d+e*x]/(e*(n-1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2,0] && NeQ[n,1] && NeQ[n,2]


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Csch[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) - 
  F^(c*(a+b*x))*Csch[d+e*x]^(n-1)*Cosh[d+e*x]/(e*(n-1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2,0] && NeQ[n,1] && NeQ[n,2]


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Sech[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Sech[d+e*x]^(n-1)*Sinh[d+e*x]/(e*(n-1)) +
  (e^2*(n-2)^2-b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2))*Int[F^(c*(a+b*x))*Sech[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2,0] && GtQ[n,1] && NeQ[n,2]


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Csch[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) - 
  F^(c*(a+b*x))*Csch[d+e*x]^(n-1)*Cosh[d+e*x]/(e*(n-1)) -
  (e^2*(n-2)^2-b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2))*Int[F^(c*(a+b*x))*Csch[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2,0] && GtQ[n,1] && NeQ[n,2]


(* Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(n*(d+e*x))/(1+E^(2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n] *)


(* Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-n*(d+e*x))/(1-E^(-2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n] *)


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*E^(n*(d+e*x))*F^(c*(a+b*x))/(e*n+b*c*Log[F])*Hypergeometric2F1[n,n/2+b*c*Log[F]/(2*e),1+n/2+b*c*Log[F]/(2*e),-E^(2*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_.,x_Symbol] :=
  (-2)^n*E^(n*(d+e*x))*F^(c*(a+b*x))/(e*n+b*c*Log[F])*Hypergeometric2F1[n,n/2+b*c*Log[F]/(2*e),1+n/2+b*c*Log[F]/(2*e),E^(2*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_.,x_Symbol] :=
  (1+E^(2*(d+e*x)))^n*Sech[d+e*x]^n/E^(n*(d+e*x))*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(n*(d+e*x))/(1+E^(2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_.,x_Symbol] :=
  (1-E^(-2*(d+e*x)))^n*Csch[d+e*x]^n/E^(-n*(d+e*x))*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-n*(d+e*x))/(1-E^(-2*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Sinh[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*f^n*Int[F^(c*(a+b*x))*Cosh[d/2+e*x/2-f*Pi/(4*g)]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f^2+g^2,0] && ILtQ[n,0]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*g^n*Int[F^(c*(a+b*x))*Cosh[d/2+e*x/2]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f-g,0] && ILtQ[n,0]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*g^n*Int[F^(c*(a+b*x))*Sinh[d/2+e*x/2]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f+g,0] && ILtQ[n,0]


Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^m_.*(f_+g_.*Sinh[d_.+e_.*x_])^n_.,x_Symbol] :=
  g^n*Int[F^(c*(a+b*x))*Tanh[d/2+e*x/2-f*Pi/(4*g)]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f^2+g^2,0] && IntegersQ[m,n] && EqQ[m+n,0]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
  g^n*Int[F^(c*(a+b*x))*Tanh[d/2+e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f-g,0] && IntegersQ[m,n] && EqQ[m+n,0]


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
  g^n*Int[F^(c*(a+b*x))*Coth[d/2+e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f+g,0] && IntegersQ[m,n] && EqQ[m+n,0]


Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Cosh[d_.+e_.*x_])/(f_+g_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
  2*i*Int[F^(c*(a+b*x))*(Cosh[d+e*x]/(f+g*Sinh[d+e*x])),x] + 
  Int[F^(c*(a+b*x))*((h-i*Cosh[d+e*x])/(f+g*Sinh[d+e*x])),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && EqQ[f^2+g^2,0] && EqQ[h^2-i^2,0] && EqQ[g*h-f*i,0]


Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Sinh[d_.+e_.*x_])/(f_+g_.*Cosh[d_.+e_.*x_]),x_Symbol] :=
  2*i*Int[F^(c*(a+b*x))*(Sinh[d+e*x]/(f+g*Cosh[d+e*x])),x] + 
  Int[F^(c*(a+b*x))*((h-i*Sinh[d+e*x])/(f+g*Cosh[d+e*x])),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && EqQ[f^2-g^2,0] && EqQ[h^2+i^2,0] && EqQ[g*h+f*i,0]


Int[F_^(c_.*u_)*G_[v_]^n_.,x_Symbol] :=
  Int[F^(c*ExpandToSum[u,x])*G[ExpandToSum[v,x]]^n,x] /;
FreeQ[{F,c,n},x] && HyperbolicQ[G] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_.,x_Symbol] :=
  Module[{u=IntHide[F^(c*(a+b*x))*Sinh[d+e*x]^n,x]},
  Dist[(f*x)^m,u,x] - f*m*Int[(f*x)^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] && GtQ[m,0]


Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_.,x_Symbol] :=
  Module[{u=IntHide[F^(c*(a+b*x))*Cosh[d+e*x]^n,x]},
  Dist[(f*x)^m,u,x] - f*m*Int[(f*x)^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] && GtQ[m,0]


Int[(f_.*x_)^m_*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_],x_Symbol] :=
  (f*x)^(m+1)/(f*(m+1))*F^(c*(a+b*x))*Sinh[d+e*x] - 
  e/(f*(m+1))*Int[(f*x)^(m+1)*F^(c*(a+b*x))*Cosh[d+e*x],x] - 
  b*c*Log[F]/(f*(m+1))*Int[(f*x)^(m+1)*F^(c*(a+b*x))*Sinh[d+e*x],x] /;
FreeQ[{F,a,b,c,d,e,f,m},x] && (LtQ[m,-1] || SumSimplerQ[m,1])


Int[(f_.*x_)^m_*F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_],x_Symbol] :=
  (f*x)^(m+1)/(f*(m+1))*F^(c*(a+b*x))*Cosh[d+e*x] - 
  e/(f*(m+1))*Int[(f*x)^(m+1)*F^(c*(a+b*x))*Sinh[d+e*x],x] - 
  b*c*Log[F]/(f*(m+1))*Int[(f*x)^(m+1)*F^(c*(a+b*x))*Cosh[d+e*x],x] /;
FreeQ[{F,a,b,c,d,e,f,m},x] && (LtQ[m,-1] || SumSimplerQ[m,1])


(* Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_.,x_Symbol] :=
  (-1)^n/2^n*Int[ExpandIntegrand[(f*x)^m*F^(c*(a+b*x)),(E^(-(d+e*x))-E^(d+e*x))^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] *)


(* Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_.,x_Symbol] :=
  1/2^n*Int[ExpandIntegrand[(f*x)^m*F^(c*(a+b*x)),(E^(-(d+e*x))+E^(d+e*x))^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] *)


Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*Cosh[f_.+g_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[F^(c*(a+b*x)),Sinh[d+e*x]^m*Cosh[f+g*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && IGtQ[m,0] && IGtQ[n,0]


Int[x_^p_.*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*Cosh[f_.+g_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^p*F^(c*(a+b*x)),Sinh[d+e*x]^m*Cosh[f+g*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[F_^(c_.*(a_.+b_.*x_))*G_[d_.+e_.*x_]^m_.*H_[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^(c*(a+b*x)),G[d+e*x]^m*H[d+e*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IGtQ[m,0] && IGtQ[n,0] && HyperbolicQ[G] && HyperbolicQ[H]


Int[F_^u_*Sinh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Sinh[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[n,0]


Int[F_^u_*Cosh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Cosh[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[n,0]


Int[F_^u_*Sinh[v_]^m_.*Cosh[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Sinh[v]^m*Cosh[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[m,0] && IGtQ[n,0]





(* ::Subsection::Closed:: *)
(*6.4.7 x^m hyper(a+b log(c x^n))^p*)


Int[Sinh[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[((c*x^n)^b/2 - 1/(2*(c*x^n)^b))^p,x] /;
FreeQ[c,x] && RationalQ[b,n,p]


Int[Cosh[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[((c*x^n)^b/2 + 1/(2*(c*x^n)^b))^p,x] /;
FreeQ[c,x] && RationalQ[b,n,p]


Int[Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  -x*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2-1) + 
  b*d*n*x*Cosh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2-1) /;
FreeQ[{a,b,c,d,n},x] && NeQ[b^2*d^2*n^2-1,0]


Int[Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  -x*Cosh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2-1) + 
  b*d*n*x*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2-1) /;
FreeQ[{a,b,c,d,n},x] && NeQ[b^2*d^2*n^2-1,0]


Int[Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
  -x*Sinh[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*n^2*p^2-1) +
  b*d*n*p*x*Cosh[d*(a+b*Log[c*x^n])]*Sinh[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*n^2*p^2-1) -
  b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2-1)*Int[Sinh[d*(a+b*Log[c*x^n])]^(p-2),x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2-1,0]


Int[Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
  -x*Cosh[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*n^2*p^2-1) +
  b*d*n*p*x*Cosh[d*(a+b*Log[c*x^n])]^(p-1)*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2*p^2-1) +
  b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2-1)*Int[Cosh[d*(a+b*Log[c*x^n])]^(p-2),x] /;
FreeQ[{a,b,c,d,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2-1,0]


Int[Sinh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  1/(2^p*b^p*d^p*p^p)*Int[ExpandIntegrand[(-E^(-a*b*d^2*p)*x^(-1/p)+E^(a*b*d^2*p)*x^(1/p))^p,x],x] /;
FreeQ[{a,b,d},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2-1,0]


Int[Cosh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  1/2^p*Int[ExpandIntegrand[(E^(-a*b*d^2*p)*x^(-1/p)+E^(a*b*d^2*p)*x^(1/p))^p,x],x] /;
FreeQ[{a,b,d},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2-1,0]


(* Int[Sinh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  E^(a*d*p)/2^p*Int[x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
FreeQ[{a,b,d},x] && IntegerQ[p] *)


(* Int[Cosh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  E^(a*d*p)/2^p*Int[x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
FreeQ[{a,b,d},x] && IntegerQ[p] *)


Int[Sinh[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
  Sinh[d*(a+b*Log[x])]^p/(x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p)*
    Int[x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]


Int[Cosh[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
  Cosh[d*(a+b*Log[x])]^p/(x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p)*
    Int[x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]


Int[Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
  x/(n*(c*x^n)^(1/n))*Subst[Int[x^(1/n-1)*Sinh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])


Int[Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
  x/(n*(c*x^n)^(1/n))*Subst[Int[x^(1/n-1)*Cosh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])


Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  -(m+1)*(e*x)^(m+1)*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2-e*(m+1)^2) + 
  b*d*n*(e*x)^(m+1)*Cosh[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2-e*(m+1)^2) /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b^2*d^2*n^2-(m+1)^2,0]


Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  -(m+1)*(e*x)^(m+1)*Cosh[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2-e*(m+1)^2) + 
  b*d*n*(e*x)^(m+1)*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2-e*(m+1)^2) /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b^2*d^2*n^2-(m+1)^2,0]


Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
  -(m+1)*(e*x)^(m+1)*Sinh[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*e*n^2*p^2-e*(m+1)^2) + 
  b*d*n*p*(e*x)^(m+1)*Cosh[d*(a+b*Log[c*x^n])]*Sinh[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*e*n^2*p^2-e*(m+1)^2) - 
  b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2-(m+1)^2)*Int[(e*x)^m*Sinh[d*(a+b*Log[c*x^n])]^(p-2),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2-(m+1)^2,0]


Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
  -(m+1)*(e*x)^(m+1)*Cosh[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*e*n^2*p^2-e*(m+1)^2) + 
  b*d*n*p*(e*x)^(m+1)*Sinh[d*(a+b*Log[c*x^n])]*Cosh[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*e*n^2*p^2-e*(m+1)^2) + 
  b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2-(m+1)^2)*Int[(e*x)^m*Cosh[d*(a+b*Log[c*x^n])]^(p-2),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2-(m+1)^2,0]


Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  (m+1)^p/(2^p*b^p*d^p*p^p)*
    Int[ExpandIntegrand[(e*x)^m*(-E^(-a*b*d^2*p/(m+1))*x^(-(m+1)/p)+E^(a*b*d^2*p/(m+1))*x^((m+1)/p))^p,x],x] /;
FreeQ[{a,b,d,e,m},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2-(m+1)^2,0]


Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  1/2^p*Int[ExpandIntegrand[(e*x)^m*(E^(-a*b*d^2*p/(m+1))*x^(-(m+1)/p)+E^(a*b*d^2*p/(m+1))*x^((m+1)/p))^p,x],x] /;
FreeQ[{a,b,d,e,m},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2-(m+1)^2,0]


(* Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  E^(a*d*p)/2^p*Int[(e*x)^m*x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
FreeQ[{a,b,d,e,m},x] && IntegerQ[p] *)


(* Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  E^(a*d*p)/2^p*Int[(e*x)^m*x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
FreeQ[{a,b,d,e,m},x] && IntegerQ[p] *)


Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
  Sinh[d*(a+b*Log[x])]^p/(x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p)*
    Int[(e*x)^m*x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]


Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
  Cosh[d*(a+b*Log[x])]^p/(x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p)*
    Int[(e*x)^m*x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]


Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
  (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n))*Subst[Int[x^((m+1)/n-1)*Sinh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])


Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
  (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n))*Subst[Int[x^((m+1)/n-1)*Cosh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])


Int[(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  -E^(-a*d)*(c*x^n)^(-b*d)/(2*x^(-b*d*n))*Int[x^(-b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] + 
  E^(a*d)*(c*x^n)^(b*d)/(2*x^(b*d*n))*Int[x^(b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,q},x]


Int[(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  E^(-a*d)*(c*x^n)^(-b*d)/(2*x^(-b*d*n))*Int[x^(-b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] + 
  E^(a*d)*(c*x^n)^(b*d)/(2*x^(b*d*n))*Int[x^(b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,q},x]


Int[(i_.*x_)^r_.*(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  -E^(-a*d)*(i*x)^r*(c*x^n)^(-b*d)/(2*x^(r-b*d*n))*Int[x^(r-b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] + 
  E^(a*d)*(i*x)^r*(c*x^n)^(b*d)/(2*x^(r+b*d*n))*Int[x^(r+b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n,q,r},x]


Int[(i_.*x_)^r_.*(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
  E^(-a*d)*(i*x)^r*(c*x^n)^(-b*d)/(2*x^(r-b*d*n))*Int[x^(r-b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] + 
  E^(a*d)*(i*x)^r*(c*x^n)^(b*d)/(2*x^(r+b*d*n))*Int[x^(r+b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n,q,r},x]


Int[Sech[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  2^p*E^(-a*d*p)*Int[x^(-b*d*p)/(1+E^(-2*a*d)*x^(-2*b*d))^p,x] /;
FreeQ[{a,b,d},x] && IntegerQ[p]


Int[Csch[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  2^p*E^(-a*d*p)*Int[x^(-b*d*p)/(1-E^(-2*a*d)*x^(-2*b*d))^p,x] /;
FreeQ[{a,b,d},x] && IntegerQ[p]


Int[Sech[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  Sech[d*(a+b*Log[x])]^p*(1+E^(-2*a*d)*x^(-2*b*d))^p/x^(-b*d*p)*
    Int[x^(-b*d*p)/(1+E^(-2*a*d)*x^(-2*b*d))^p,x] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]


Int[Csch[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  Csch[d*(a+b*Log[x])]^p*(1-E^(-2*a*d)*x^(-2*b*d))^p/x^(-b*d*p)*
    Int[x^(-b*d*p)/(1-E^(-2*a*d)*x^(-2*b*d))^p,x] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]


Int[Sech[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
  x/(n*(c*x^n)^(1/n))*Subst[Int[x^(1/n-1)*Sech[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])


Int[Csch[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
  x/(n*(c*x^n)^(1/n))*Subst[Int[x^(1/n-1)*Csch[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])


Int[(e_.*x_)^m_.*Sech[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  2^p*E^(-a*d*p)*Int[(e*x)^m*x^(-b*d*p)/(1+E^(-2*a*d)*x^(-2*b*d))^p,x] /;
FreeQ[{a,b,d,e,m},x] && IntegerQ[p]


Int[(e_.*x_)^m_.*Csch[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  2^p*E^(-a*d*p)*Int[(e*x)^m*x^(-b*d*p)/(1-E^(-2*a*d)*x^(-2*b*d))^p,x] /;
FreeQ[{a,b,d,e,m},x] && IntegerQ[p]


Int[(e_.*x_)^m_.*Sech[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  Sech[d*(a+b*Log[x])]^p*(1+E^(-2*a*d)*x^(-2*b*d))^p/x^(-b*d*p)*
    Int[(e*x)^m*x^(-b*d*p)/(1+E^(-2*a*d)*x^(-2*b*d))^p,x] /;
FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]


Int[(e_.*x_)^m_.*Csch[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
  Csch[d*(a+b*Log[x])]^p*(1-E^(-2*a*d)*x^(-2*b*d))^p/x^(-b*d*p)*
    Int[(e*x)^m*x^(-b*d*p)/(1-E^(-2*a*d)*x^(-2*b*d))^p,x] /;
FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]


Int[(e_.*x_)^m_.*Sech[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
  (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n))*Subst[Int[x^((m+1)/n-1)*Sech[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])


Int[(e_.*x_)^m_.*Csch[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
  (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n))*Subst[Int[x^((m+1)/n-1)*Csch[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])


Int[Sinh[a_.*x_*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
  Cosh[a*x*Log[b*x]]/a - Int[Sinh[a*x*Log[b*x]],x] /;
FreeQ[{a,b},x]


Int[Cosh[a_.*x_*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
  Sinh[a*x*Log[b*x]]/a - Int[Cosh[a*x*Log[b*x]],x] /;
FreeQ[{a,b},x]


Int[x_^m_.*Sinh[a_.*x_^n_.*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
  Cosh[a*x^n*Log[b*x]]/(a*n) - 1/n*Int[x^m*Sinh[a*x^n*Log[b*x]],x] /;
FreeQ[{a,b,m,n},x] && EqQ[m,n-1]


Int[x_^m_.*Cosh[a_.*x_^n_.*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
  Sinh[a*x^n*Log[b*x]]/(a*n) - 1/n*Int[x^m*Cosh[a*x^n*Log[b*x]],x] /;
FreeQ[{a,b,m,n},x] && EqQ[m,n-1]





(* ::Subsection::Closed:: *)
(*6.4.8 Active hyperbolic functions*)


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Sinh[c+d*x]^(n-1),x] - a/b*Int[(e+f*x)^m*Sinh[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Cosh[c+d*x]^(n-1),x] - a/b*Int[(e+f*x)^m*Cosh[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  -(e+f*x)^(m+1)/(b*f*(m+1)) + 2*Int[(e+f*x)^m*E^(c+d*x)/(a+b*E^(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[a^2+b^2,0]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  -(e+f*x)^(m+1)/(b*f*(m+1)) + 2*Int[(e+f*x)^m*E^(c+d*x)/(a+b*E^(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[a^2-b^2,0]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  -(e+f*x)^(m+1)/(b*f*(m+1)) + 
  Int[(e+f*x)^m*E^(c+d*x)/(a-Rt[a^2+b^2,2]+b*E^(c+d*x)),x] + 
  Int[(e+f*x)^m*E^(c+d*x)/(a+Rt[a^2+b^2,2]+b*E^(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2+b^2,0]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  -(e+f*x)^(m+1)/(b*f*(m+1)) + 
  Int[(e+f*x)^m*E^(c+d*x)/(a-Rt[a^2-b^2,2]+b*E^(c+d*x)),x] + 
  Int[(e+f*x)^m*E^(c+d*x)/(a+Rt[a^2-b^2,2]+b*E^(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2-b^2,0]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^n_/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2),x] + 
  1/b*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)*Sinh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[n,1] && EqQ[a^2+b^2,0]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^n_/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  -1/a*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2),x] + 
  1/b*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)*Cosh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[n,1] && EqQ[a^2-b^2,0]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^n_/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  -a/b^2*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2),x] + 
  1/b*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)*Sinh[c+d*x],x] + 
  (a^2+b^2)/b^2*Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[n,1] && NeQ[a^2+b^2,0] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^n_/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  -a/b^2*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2),x] + 
  1/b*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)*Cosh[c+d*x],x] + 
  (a^2-b^2)/b^2*Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[n,1] && NeQ[a^2-b^2,0] && IGtQ[m,0]


Int[(e_.+f_.*x_)^m_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Sech[c+d*x]*Tanh[c+d*x]^(n-1),x] - a/b*Int[(e+f*x)^m*Sech[c+d*x]*Tanh[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Csch[c+d*x]*Coth[c+d*x]^(n-1),x] - a/b*Int[(e+f*x)^m*Csch[c+d*x]*Coth[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Coth[c+d*x]^n,x] - b/a*Int[(e+f*x)^m*Cosh[c+d*x]*Coth[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Tanh[c+d*x]^n,x] - b/a*Int[(e+f*x)^m*Sinh[c+d*x]*Tanh[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Sech[c+d*x]^(n+2),x] + 
  1/b*Int[(e+f*x)^m*Sech[c+d*x]^(n+1)*Tanh[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && EqQ[a^2+b^2,0]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  -1/a*Int[(e+f*x)^m*Csch[c+d*x]^(n+2),x] + 
  1/b*Int[(e+f*x)^m*Csch[c+d*x]^(n+1)*Coth[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && EqQ[a^2-b^2,0]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  b^2/(a^2+b^2)*Int[(e+f*x)^m*Sech[c+d*x]^(n-2)/(a+b*Sinh[c+d*x]),x] + 
  1/(a^2+b^2)*Int[(e+f*x)^m*Sech[c+d*x]^n*(a-b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2+b^2,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  b^2/(a^2-b^2)*Int[(e+f*x)^m*Csch[c+d*x]^(n-2)/(a+b*Cosh[c+d*x]),x] + 
  1/(a^2-b^2)*Int[(e+f*x)^m*Csch[c+d*x]^n*(a-b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2-b^2,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Csch[c+d*x]^n,x] - b/a*Int[(e+f*x)^m*Csch[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Sech[c+d*x]^n,x] - b/a*Int[(e+f*x)^m*Sech[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]


Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  Unintegrable[(e+f*x)^m*F[c+d*x]^n/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && HyperbolicQ[F]


Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  Unintegrable[(e+f*x)^m*F[c+d*x]^n/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && HyperbolicQ[F]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^p_.*Sinh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Cosh[c+d*x]^p*Sinh[c+d*x]^(n-1),x] - 
  a/b*Int[(e+f*x)^m*Cosh[c+d*x]^p*Sinh[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^p_.*Cosh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Sinh[c+d*x]^p*Cosh[c+d*x]^(n-1),x] - 
  a/b*Int[(e+f*x)^m*Sinh[c+d*x]^p*Cosh[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^p_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Sinh[c+d*x]^(p-1)*Tanh[c+d*x]^n,x] - 
  a/b*Int[(e+f*x)^m*Sinh[c+d*x]^(p-1)*Tanh[c+d*x]^n/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^p_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Cosh[c+d*x]^(p-1)*Coth[c+d*x]^n,x] - 
  a/b*Int[(e+f*x)^m*Cosh[c+d*x]^(p-1)*Coth[c+d*x]^n/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^p_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Sech[c+d*x]^(p+1)*Tanh[c+d*x]^(n-1),x] - 
  a/b*Int[(e+f*x)^m*Sech[c+d*x]^(p+1)*Tanh[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^p_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/b*Int[(e+f*x)^m*Csch[c+d*x]^(p+1)*Coth[c+d*x]^(n-1),x] - 
  a/b*Int[(e+f*x)^m*Csch[c+d*x]^(p+1)*Coth[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^p_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Cosh[c+d*x]^p*Coth[c+d*x]^n,x] - 
  b/a*Int[(e+f*x)^m*Cosh[c+d*x]^(p+1)*Coth[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^p_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Sinh[c+d*x]^p*Tanh[c+d*x]^n,x] - 
  b/a*Int[(e+f*x)^m*Sinh[c+d*x]^(p+1)*Tanh[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^p_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Csch[c+d*x]^p*Coth[c+d*x]^n,x] - 
  b/a*Int[(e+f*x)^m*Csch[c+d*x]^(p-1)*Coth[c+d*x]^n/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^p_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Sech[c+d*x]^p*Tanh[c+d*x]^n,x] - 
  b/a*Int[(e+f*x)^m*Sech[c+d*x]^(p-1)*Tanh[c+d*x]^n/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^p_.*Csch[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Sech[c+d*x]^p*Csch[c+d*x]^n,x] - 
  b/a*Int[(e+f*x)^m*Sech[c+d*x]^p*Csch[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^p_.*Sech[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Csch[c+d*x]^p*Sech[c+d*x]^n,x] - 
  b/a*Int[(e+f*x)^m*Csch[c+d*x]^p*Sech[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]


Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
  Unintegrable[(e+f*x)^m*F[c+d*x]^n*G[c+d*x]^p/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && HyperbolicQ[F] && HyperbolicQ[G]


Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
  Unintegrable[(e+f*x)^m*F[c+d*x]^n*G[c+d*x]^p/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && HyperbolicQ[F] && HyperbolicQ[G]


Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Sech[c_.+d_.*x_]),x_Symbol] :=
  Int[(e+f*x)^m*Cosh[c+d*x]*F[c+d*x]^n/(b+a*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && HyperbolicQ[F] && IntegersQ[m,n]


Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Csch[c_.+d_.*x_]),x_Symbol] :=
  Int[(e+f*x)^m*Sinh[c+d*x]*F[c+d*x]^n/(b+a*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && HyperbolicQ[F] && IntegersQ[m,n]


Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Sech[c_.+d_.*x_]),x_Symbol] :=
  Int[(e+f*x)^m*Cosh[c+d*x]*F[c+d*x]^n*G[c+d*x]^p/(b+a*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && HyperbolicQ[F] && HyperbolicQ[G] && IntegersQ[m,n,p]


Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Csch[c_.+d_.*x_]),x_Symbol] :=
  Int[(e+f*x)^m*Sinh[c+d*x]*F[c+d*x]^n*G[c+d*x]^p/(b+a*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && HyperbolicQ[F] && HyperbolicQ[G] && IntegersQ[m,n,p]


Int[Sinh[a_.+b_.*x_]^p_.*Sinh[c_.+d_.*x_]^q_.,x_Symbol] :=
  1/2^(p+q)*Int[ExpandIntegrand[(-E^(-c-d*x)+E^(c+d*x))^q,(-E^(-a-b*x)+E^(a+b*x))^p,x],x] /;
FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]


Int[Cosh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
  1/2^(p+q)*Int[ExpandIntegrand[(E^(-c-d*x)+E^(c+d*x))^q,(E^(-a-b*x)+E^(a+b*x))^p,x],x] /;
FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]


Int[Sinh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
  1/2^(p+q)*Int[ExpandIntegrand[(E^(-c-d*x)+E^(c+d*x))^q,(-E^(-a-b*x)+E^(a+b*x))^p,x],x] /;
FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]


Int[Cosh[a_.+b_.*x_]^p_.*Sinh[c_.+d_.*x_]^q_.,x_Symbol] :=
  1/2^(p+q)*Int[ExpandIntegrand[(-E^(-c-d*x)+E^(c+d*x))^q,(E^(-a-b*x)+E^(a+b*x))^p,x],x] /;
FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]


Int[Sinh[a_.+b_.*x_]*Tanh[c_.+d_.*x_],x_Symbol] :=
  Int[-E^(-(a+b*x))/2 + E^(a+b*x)/2 + E^(-(a+b*x))/(1+E^(2*(c+d*x))) - E^(a+b*x)/(1+E^(2*(c+d*x))),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]


Int[Cosh[a_.+b_.*x_]*Coth[c_.+d_.*x_],x_Symbol] :=
  Int[E^(-(a+b*x))/2 + E^(a+b*x)/2 - E^(-(a+b*x))/(1-E^(2*(c+d*x))) - E^(a+b*x)/(1-E^(2*(c+d*x))),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]


Int[Sinh[a_.+b_.*x_]*Coth[c_.+d_.*x_],x_Symbol] :=
  Int[-E^(-(a+b*x))/2 + E^(a+b*x)/2 + E^(-(a+b*x))/(1-E^(2*(c+d*x))) - E^(a+b*x)/(1-E^(2*(c+d*x))),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]


Int[Cosh[a_.+b_.*x_]*Tanh[c_.+d_.*x_],x_Symbol] :=
  Int[E^(-(a+b*x))/2 + E^(a+b*x)/2 - E^(-(a+b*x))/(1+E^(2*(c+d*x))) - E^(a+b*x)/(1+E^(2*(c+d*x))),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]


Int[Sinh[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Sinh[a*x]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,c,d},x] && IGtQ[n,0]


Int[Cosh[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Cosh[a*x]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,c,d},x] && IGtQ[n,0]


Int[Sinh[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Sinh[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,b,c,d},x] && IGtQ[n,0] && NeQ[b*c-a*d,0]


Int[Cosh[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Cosh[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,b,c,d},x] && IGtQ[n,0] && NeQ[b*c-a*d,0]


Int[Sinh[u_]^n_.,x_Symbol] :=
  With[{lst=QuotientOfLinearsParts[u,x]},
  Int[Sinh[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
IGtQ[n,0] && QuotientOfLinearsQ[u,x]


Int[Cosh[u_]^n_.,x_Symbol] :=
  With[{lst=QuotientOfLinearsParts[u,x]},
  Int[Cosh[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
IGtQ[n,0] && QuotientOfLinearsQ[u,x]


Int[u_.*Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
  Int[u*Sinh[v]^(p+q),x] /;
EqQ[w,v]


Int[u_.*Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[u*Cosh[v]^(p+q),x] /;
EqQ[w,v]


Int[Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Sinh[v]^p*Sinh[w]^q,x],x] /;
IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Cosh[v]^p*Cosh[w]^q,x],x] /;
IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sinh[v]^p*Sinh[w]^q,x],x] /;
IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Cosh[v]^p*Cosh[w]^q,x],x] /;
IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[u_.*Sinh[v_]^p_.*Cosh[w_]^p_.,x_Symbol] :=
  1/2^p*Int[u*Sinh[2*v]^p,x] /;
EqQ[w,v] && IntegerQ[p]


Int[Sinh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Sinh[v]^p*Cosh[w]^q,x],x] /;
IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Sinh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sinh[v]^p*Cosh[w]^q,x],x] /;
IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[Sinh[v_]*Tanh[w_]^n_.,x_Symbol] :=
  Int[Cosh[v]*Tanh[w]^(n-1),x] - Cosh[v-w]*Int[Sech[w]*Tanh[w]^(n-1),x] /;
GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]


Int[Cosh[v_]*Coth[w_]^n_.,x_Symbol] :=
  Int[Sinh[v]*Coth[w]^(n-1),x] + Cosh[v-w]*Int[Csch[w]*Coth[w]^(n-1),x] /;
GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]


Int[Sinh[v_]*Coth[w_]^n_.,x_Symbol] :=
  Int[Cosh[v]*Coth[w]^(n-1),x] + Sinh[v-w]*Int[Csch[w]*Coth[w]^(n-1),x] /;
GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]


Int[Cosh[v_]*Tanh[w_]^n_.,x_Symbol] :=
  Int[Sinh[v]*Tanh[w]^(n-1),x] - Sinh[v-w]*Int[Sech[w]*Tanh[w]^(n-1),x] /;
GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]


Int[Sinh[v_]*Sech[w_]^n_.,x_Symbol] :=
  Cosh[v-w]*Int[Tanh[w]*Sech[w]^(n-1),x] + Sinh[v-w]*Int[Sech[w]^(n-1),x] /;
GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]


Int[Cosh[v_]*Csch[w_]^n_.,x_Symbol] :=
  Cosh[v-w]*Int[Coth[w]*Csch[w]^(n-1),x] + Sinh[v-w]*Int[Csch[w]^(n-1),x] /;
GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]


Int[Sinh[v_]*Csch[w_]^n_.,x_Symbol] :=
  Sinh[v-w]*Int[Coth[w]*Csch[w]^(n-1),x] + Cosh[v-w]*Int[Csch[w]^(n-1),x] /;
GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]


Int[Cosh[v_]*Sech[w_]^n_.,x_Symbol] :=
  Sinh[v-w]*Int[Tanh[w]*Sech[w]^(n-1),x] + Cosh[v-w]*Int[Sech[w]^(n-1),x] /;
GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sinh[c_.+d_.*x_]*Cosh[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(e+f*x)^m*(a+b*Sinh[2*c+2*d*x]/2)^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a-b+b*Cosh[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NeQ[a-b,0] && IGtQ[m,0] && ILtQ[n,0] && (EqQ[n,-1] || EqQ[m,1] && EqQ[n,-2])


Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a+b+b*Cosh[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NeQ[a-b,0] && IGtQ[m,0] && ILtQ[n,0] && (EqQ[n,-1] || EqQ[m,1] && EqQ[n,-2])


Int[(f_.+g_.*x_)^m_./(a_.+b_.*Cosh[d_.+e_.*x_]^2+c_.*Sinh[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]


Int[(f_.+g_.*x_)^m_.*Sech[d_.+e_.*x_]^2/(b_+c_.*Tanh[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{b,c,d,e,f,g},x] && IGtQ[m,0]


Int[(f_.+g_.*x_)^m_.*Sech[d_.+e_.*x_]^2/(b_.+a_.*Sech[d_.+e_.*x_]^2+c_.*Tanh[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]


Int[(f_.+g_.*x_)^m_.*Csch[d_.+e_.*x_]^2/(c_+b_.*Coth[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{b,c,d,e,f,g},x] && IGtQ[m,0]


Int[(f_.+g_.*x_)^m_.*Csch[d_.+e_.*x_]^2/(c_.+b_.*Coth[d_.+e_.*x_]^2+a_.*Csch[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]


Int[(e_.+f_.*x_)*(A_+B_.*Sinh[c_.+d_.*x_])/(a_+b_.*Sinh[c_.+d_.*x_])^2,x_Symbol] :=
  B*(e+f*x)*Cosh[c+d*x]/(a*d*(a+b*Sinh[c+d*x])) - 
  B*f/(a*d)*Int[Cosh[c+d*x]/(a+b*Sinh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[a*A+b*B,0]


Int[(e_.+f_.*x_)*(A_+B_.*Cosh[c_.+d_.*x_])/(a_+b_.*Cosh[c_.+d_.*x_])^2,x_Symbol] :=
  B*(e+f*x)*Sinh[c+d*x]/(a*d*(a+b*Cosh[c+d*x])) -
  B*f/(a*d)*Int[Sinh[c+d*x]/(a+b*Cosh[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[a*A-b*B,0]


Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d^(m+1)*Subst[Int[(d*e-c*f+f*x)^m*Sinh[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && RationalQ[p]


Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d^(m+1)*Subst[Int[(d*e-c*f+f*x)^m*Cosh[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && RationalQ[p]


Int[Sech[v_]^m_.*(a_+b_.*Tanh[v_])^n_.,x_Symbol] :=
  Int[(a*Cosh[v]+b*Sinh[v])^n,x] /;
FreeQ[{a,b},x] && IntegerQ[(m-1)/2] && EqQ[m+n,0]


Int[Csch[v_]^m_.*(a_+b_.*Coth[v_])^n_.,x_Symbol] :=
  Int[(b*Cosh[v]+a*Sinh[v])^n,x] /;
FreeQ[{a,b},x] && IntegerQ[(m-1)/2] && EqQ[m+n,0]


Int[u_.*Sinh[a_.+b_.*x_]^m_.*Sinh[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[u,Sinh[a+b*x]^m*Sinh[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0] && IGtQ[n,0]


Int[u_.*Cosh[a_.+b_.*x_]^m_.*Cosh[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[u,Cosh[a+b*x]^m*Cosh[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && IGtQ[m,0] && IGtQ[n,0]


Int[Sech[a_.+b_.*x_]*Sech[c_+d_.*x_],x_Symbol] :=
  -Csch[(b*c-a*d)/d]*Int[Tanh[a+b*x],x] + Csch[(b*c-a*d)/b]*Int[Tanh[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]


Int[Csch[a_.+b_.*x_]*Csch[c_+d_.*x_],x_Symbol] :=
  Csch[(b*c-a*d)/b]*Int[Coth[a+b*x],x] - Csch[(b*c-a*d)/d]*Int[Coth[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]


Int[Tanh[a_.+b_.*x_]*Tanh[c_+d_.*x_],x_Symbol] :=
  b*x/d - b/d*Cosh[(b*c-a*d)/d]*Int[Sech[a+b*x]*Sech[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]


Int[Coth[a_.+b_.*x_]*Coth[c_+d_.*x_],x_Symbol] :=
  b*x/d + Cosh[(b*c-a*d)/d]*Int[Csch[a+b*x]*Csch[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]


Int[u_.*(a_.*Cosh[v_]+b_.*Sinh[v_])^n_.,x_Symbol] :=
  Int[u*(a*E^(a/b*v))^n,x] /;
FreeQ[{a,b,n},x] && EqQ[a^2-b^2,0]


Int[Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
  -1/2*Int[E^(-d*(a+b*Log[c*x^n])^2),x] + 1/2*Int[E^(d*(a+b*Log[c*x^n])^2),x] /;
FreeQ[{a,b,c,d,n},x]


Int[Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
  1/2*Int[E^(-d*(a+b*Log[c*x^n])^2),x] + 1/2*Int[E^(d*(a+b*Log[c*x^n])^2),x] /;
FreeQ[{a,b,c,d,n},x]


Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
  -1/2*Int[(e*x)^m*E^(-d*(a+b*Log[c*x^n])^2),x] + 1/2*Int[(e*x)^m*E^(d*(a+b*Log[c*x^n])^2),x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(-d*(a+b*Log[c*x^n])^2),x] + 1/2*Int[(e*x)^m*E^(d*(a+b*Log[c*x^n])^2),x] /;
FreeQ[{a,b,c,d,e,m,n},x]



