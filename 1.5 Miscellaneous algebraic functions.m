(* ::Package:: *)

(* ::Section:: *)
(*Miscellaneous Algebraic Function Rules*)


(* ::Subsection::Closed:: *)
(*5.4 Normalizing algebraic functions*)


Int[(a_.+b_.*(c_.*x_^n_)^q_)^p_.,x_Symbol] :=
  x/(c*x^n)^(1/n)*Subst[Int[(a+b*x^(n*q))^p,x],x,(c*x^n)^(1/n)] /;
FreeQ[{a,b,c,q,n,p},x] && IntegerQ[n*q]


Int[x_^m_.*(a_.+b_.*(c_.*x_^n_)^q_)^p_.,x_Symbol] :=
  x^(m+1)/(c*x^n)^((m+1)/n)*Subst[Int[x^m*(a+b*x^(n*q))^p,x],x,(c*x^n)^(1/n)] /;
FreeQ[{a,b,c,m,n,p,q},x] && IntegerQ[n*q] && IntegerQ[m]


Int[x_^m_.*(e_.*(a_+b_.*x_^n_.)^r_.)^p_*(f_.*(c_+d_.*x_^n_.)^s_)^q_,x_Symbol] :=
  (e*(a+b*x^n)^r)^p*(f*(c+d*x^n)^s)^q/((a+b*x^n)^(p*r)*(c+d*x^n)^(q*s))*
    Int[x^m*(a+b*x^n)^(p*r)*(c+d*x^n)^(q*s),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r,s},x]


Int[u_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  (b*e/d)^p*Int[u,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*c-a*d]


Int[u_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  Int[u*(e*(a+b*x^n))^p/(c+d*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && PositiveQ[b*d*e] && PositiveQ[c-a*d/b]


Int[(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  With[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[
    Int[x^(q*(p+1)-1)*(-a*e+c*x^q)^(1/n-1)/(b*e-d*x^q)^(1/n+1),x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && FractionQ[p] && IntegerQ[1/n]


Int[x_^m_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  With[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[
    Int[x^(q*(p+1)-1)*(-a*e+c*x^q)^(Simplify[(m+1)/n]-1)/(b*e-d*x^q)^(Simplify[(m+1)/n]+1),x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e,m,n},x] && FractionQ[p] && IntegerQ[Simplify[(m+1)/n]]


Int[u_^r_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  With[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[Int[SimplifyIntegrand[x^(q*(p+1)-1)*(-a*e+c*x^q)^(1/n-1)/(b*e-d*x^q)^(1/n+1)*
    ReplaceAll[u,x->(-a*e+c*x^q)^(1/n)/(b*e-d*x^q)^(1/n)]^r,x],x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[u,x] && FractionQ[p] && IntegerQ[1/n] && IntegerQ[r]


Int[x_^m_.*u_^r_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  With[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[Int[SimplifyIntegrand[x^(q*(p+1)-1)*(-a*e+c*x^q)^((m+1)/n-1)/(b*e-d*x^q)^((m+1)/n+1)*
    ReplaceAll[u,x->(-a*e+c*x^q)^(1/n)/(b*e-d*x^q)^(1/n)]^r,x],x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[u,x] && FractionQ[p] && IntegerQ[1/n] && IntegersQ[m,r]


Int[(a_.+b_.*(c_./x_)^n_)^p_,x_Symbol] :=
  -c*Subst[Int[(a+b*x^n)^p/x^2,x],x,c/x] /;
FreeQ[{a,b,c,n,p},x]


Int[x_^m_.*(a_.+b_.*(c_./x_)^n_)^p_.,x_Symbol] :=
  -c^(m+1)*Subst[Int[(a+b*x^n)^p/x^(m+2),x],x,c/x] /;
FreeQ[{a,b,c,n,p},x] && IntegerQ[m]


Int[(d_.*x_)^m_*(a_.+b_.*(c_./x_)^n_)^p_.,x_Symbol] :=
  -c*(d*x)^m*(c/x)^m*Subst[Int[(a+b*x^n)^p/x^(m+2),x],x,c/x] /;
FreeQ[{a,b,c,d,m,n,p},x] && Not[IntegerQ[m]]


Int[(a_.+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_.,x_Symbol] :=
  -d*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^2,x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[n2-2*n]


Int[x_^m_.*(a_+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_.,x_Symbol] :=
  -d^(m+1)*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[n2-2*n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_.,x_Symbol] :=
  -d*(e*x)^m*(d/x)^m*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && Not[IntegerQ[m]]


Int[(a_.+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  -d*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^2,x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[n2+2*n] && IntegerQ[2*n]


Int[x_^m_.*(a_+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  -d^(m+1)*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[n2+2*n] && IntegerQ[2*n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  -d*(e*x)^m*(d/x)^m*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[n2+2*n] && Not[IntegerQ[m]] && IntegerQ[2*n]


Int[u_^m_,x_Symbol] :=
  Int[ExpandToSum[u,x]^m,x] /;
FreeQ[m,x] && LinearQ[u,x] && Not[LinearMatchQ[u,x]]


Int[u_^m_.*v_^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n,x] /;
FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
FreeQ[{m,n,p},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[u_^m_.*v_^n_.*w_^p_.*z_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p*ExpandToSum[z,x]^q,x] /;
FreeQ[{m,n,p,q},x] && LinearQ[{u,v,w,z},x] && Not[LinearMatchQ[{u,v,w,z},x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
FreeQ[{m,n,p},x] && LinearQ[{u,v},x] && QuadraticQ[w,x] && Not[LinearMatchQ[{u,v},x] && QuadraticMatchQ[w,x]]


Int[u_^p_.*v_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{p,q},x] && QuadraticQ[{u,v},x] && Not[QuadraticMatchQ[{u,v},x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(c_.*x_)^m_.*u_^p_.,x_Symbol] :=
  Int[(c*x)^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{c,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[u_^p_.*v_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{p,q},x] && BinomialQ[{u,v},x] && ZeroQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && Not[BinomialMatchQ[{u,v},x]]


Int[x_^m_.*u_^p_.*v_^q_.,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{m,p,q},x] && BinomialQ[{u,v},x] && ZeroQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && Not[BinomialMatchQ[{u,v},x]]


Int[u_^m_.*v_^p_.*w_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p*ExpandToSum[w,x]^q,x] /;
FreeQ[{m,p,q},x] && BinomialQ[{u,v,w},x] && ZeroQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && 
  ZeroQ[BinomialDegree[u,x]-BinomialDegree[w,x]] && Not[BinomialMatchQ[{u,v,w},x]]


Int[x_^m_.*u_^p_.*v_^q_.*z_^r_.,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q*ExpandToSum[z,x]^r,x] /;
FreeQ[{m,p,q,r},x] && BinomialQ[{u,v,z},x] && ZeroQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && 
  ZeroQ[BinomialDegree[u,x]-BinomialDegree[z,x]] && Not[BinomialMatchQ[{u,v,z},x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && GeneralizedBinomialQ[u,x] && Not[GeneralizedBinomialMatchQ[u,x]]


Int[x_^m_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p},x] && GeneralizedBinomialQ[u,x] && Not[GeneralizedBinomialMatchQ[u,x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]


Int[(d_.*x_)^m_.*u_^p_.,x_Symbol] :=
  Int[(d*x)^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{d,m,p},x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]


Int[u_^q_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^q*ExpandToSum[v,x]^p,x] /;
FreeQ[{p,q},x] && BinomialQ[u,x] && TrinomialQ[v,x] && Not[BinomialMatchQ[u,x] && TrinomialMatchQ[v,x]]


Int[u_^q_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^q*ExpandToSum[v,x]^p,x] /;
FreeQ[{p,q},x] && BinomialQ[u,x] && BinomialQ[v,x] && Not[BinomialMatchQ[u,x] && BinomialMatchQ[v,x]]


Int[x_^m_.*z_^q_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p,q},x] && BinomialQ[z,x] && TrinomialQ[u,x] && Not[BinomialMatchQ[z,x] && TrinomialMatchQ[u,x]]


Int[x_^m_.*z_^q_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p,q},x] && BinomialQ[z,x] && BinomialQ[u,x] && Not[BinomialMatchQ[z,x] && BinomialMatchQ[u,x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && GeneralizedTrinomialQ[u,x] && Not[GeneralizedTrinomialMatchQ[u,x]]


Int[x_^m_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p},x] && GeneralizedTrinomialQ[u,x] && Not[GeneralizedTrinomialMatchQ[u,x]]


Int[z_*u_^p_.,x_Symbol] :=
  Int[ExpandToSum[z,x]*ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && BinomialQ[z,x] && GeneralizedTrinomialQ[u,x] && 
  ZeroQ[BinomialDegree[z,x]-GeneralizedTrinomialDegree[u,x]] && Not[BinomialMatchQ[z,x] && GeneralizedTrinomialMatchQ[u,x]]


Int[x_^m_.*z_*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[z,x]*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p},x] && BinomialQ[z,x] && GeneralizedTrinomialQ[u,x] && 
  ZeroQ[BinomialDegree[z,x]-GeneralizedTrinomialDegree[u,x]] && Not[BinomialMatchQ[z,x] && GeneralizedTrinomialMatchQ[u,x]]





(* ::Subsection::Closed:: *)
(*3.7 (c x)^m Pq(x) (a+b x^n)^p*)


Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_)^p_,x_Symbol] :=
  With[{n=Denominator[p]},
  n/b*Subst[Int[x^(n*p+n-1)*(-a*c/b+c*x^n/b)^m*ReplaceAll[Pq,x->-a/b+x^n/b],x],x,(a+b*x)^(1/n)]] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && FractionQ[p] && NegativeIntegerQ[m+1]


(* Int[Pq_*(a_+b_.*x_)^p_,x_Symbol] :=
  With[{n=Denominator[p]},
  n/b*Subst[Int[x^(n*p+n-1)*ReplaceAll[Pq,x->-a/b+x^n/b],x],x,(a+b*x)^(1/n)]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && FractionQ[p] *)


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  1/(m+1)*Subst[Int[SubstFor[x^(m+1),Pq,x]*(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && PolyQ[Pq,x^(m+1)]


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Coeff[Pq,x,n-1]*(a+b*x^n)^(p+1)/(b*n*(p+1)) + 
  Int[ExpandToSum[Pq-Coeff[Pq,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n,p] && NonzeroQ[Coeff[Pq,x,n-1]]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PolyQ[Pq,x] && (PositiveIntegerQ[p] || ZeroQ[n-1])


Int[Pq_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,n},x] && PolyQ[Pq,x] && (PositiveIntegerQ[p] || ZeroQ[n-1])


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Pq,x]*(a+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[(m+1)/n]]


Int[(c_*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*Pq*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Pq*(a+b*x^n)^(p+1)/(b*n*(p+1)) - 
  1/(b*n*(p+1))*Int[D[Pq,x]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,m,n},x] && PolyQ[Pq,x] && ZeroQ[m-n+1] && RationalQ[p] && p<-1


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  1/d*Int[(d*x)^(m+1)*ExpandToSum[Pq/x,x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b,d,m,n,p},x] && PolyQ[Pq,x] && ZeroQ[Coeff[Pq,x,0]]


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Int[x*ExpandToSum[Pq/x,x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b,n,p},x] && PolyQ[Pq,x] && ZeroQ[Coeff[Pq,x,0]] && SumQ[Pq]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Module[{u=IntHide[x^m*Pq,x]},
  u*(a+b*x^n)^p - b*n*p*Int[x^(m+n)*(a+b*x^n)^(p-1)*ExpandToSum[u/x^(m+1),x],x]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m+Expon[Pq,x]+1<0


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],i},
  (c*x)^m*(a+b*x^n)^p*Sum[Coeff[Pq,x,i]*x^(i+1)/(m+n*p+i+1),{i,0,q}] + 
  a*n*p*Int[(c*x)^m*(a+b*x^n)^(p-1)*Sum[Coeff[Pq,x,i]*x^i/(m+n*p+i+1),{i,0,q}],x]] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && PositiveIntegerQ[(n-1)/2] && RationalQ[p] && p>0


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],i},
  (a+b*x^n)^p*Sum[Coeff[Pq,x,i]*x^(i+1)/(n*p+i+1),{i,0,q}] + 
  a*n*p*Int[(a+b*x^n)^(p-1)*Sum[Coeff[Pq,x,i]*x^i/(n*p+i+1),{i,0,q}],x]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[(n-1)/2] && RationalQ[p] && p>0


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],i},
  (a*Coeff[Pq,x,q]-b*x*ExpandToSum[Pq-Coeff[Pq,x,q]*x^q,x])*(a+b*x^n)^(p+1)/(a*b*n*(p+1)) + 
  1/(a*n*(p+1))*Int[Sum[(n*(p+1)+i+1)*Coeff[Pq,x,i]*x^i,{i,0,q-1}]*(a+b*x^n)^(p+1),x] /;
 q==n-1] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  -x*Pq*(a+b*x^n)^(p+1)/(a*n*(p+1)) + 
  1/(a*n*(p+1))*Int[ExpandToSum[n*(p+1)*Pq+D[x*Pq,x],x]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && Expon[Pq,x]<n-1


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Module[{Q=PolynomialQuotient[b^(Floor[(q-1)/n]+1)*Pq,a+b*x^n,x],R=PolynomialRemainder[b^(Floor[(q-1)/n]+1)*Pq,a+b*x^n,x],i},
  -x*R*(a+b*x^n)^(p+1)/(a*n*(p+1)*b^(Floor[(q-1)/n]+1)) + 
  1/(a*n*(p+1)*b^(Floor[(q-1)/n]+1))*Int[(a+b*x^n)^(p+1)*ExpandToSum[a*n*(p+1)*Q+n*(p+1)*R+D[x*R,x],x],x]] /;
 q>=n] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[x_^m_*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Module[{Q=PolynomialQuotient[a*b^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n,x],
          R=PolynomialRemainder[a*b^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n,x],i},
  -x*R*(a+b*x^n)^(p+1)/(a^2*n*(p+1)*b^(Floor[(q-1)/n]+1)) + 
  1/(a*n*(p+1)*b^(Floor[(q-1)/n]+1))*Int[x^m*(a+b*x^n)^(p+1)*
    ExpandToSum[n*(p+1)*x^(-m)*Q+Sum[(n*(p+1)+i+1)/a*Coeff[R,x,i]*x^(i-m),{i,0,n-1}],x],x]]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && NegativeIntegerQ[m]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=GCD[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*ReplaceAll[Pq,x->x^(1/g)]*(a+b*x^(n/g))^p,x],x,x^g] /;
 g!=1] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x^n] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  B^3/b*Int[1/(A^2-A*B*x+B^2*x^2),x] /;
FreeQ[{a,b,A,B},x] && ZeroQ[a*B^3-b*A^3]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  -r*(B*r-A*s)/(3*a*s)*Int[1/(r+s*x),x] + 
  r/(3*a*s)*Int[(r*(B*r+2*A*s)+s*(B*r-A*s)*x)/(r^2-r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b,A,B},x] && NonzeroQ[a*B^3-b*A^3] && PosQ[a/b]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r*(B*r+A*s)/(3*a*s)*Int[1/(r-s*x),x] - 
  r/(3*a*s)*Int[(r*(B*r-2*A*s)-s*(B*r+A*s)*x)/(r^2+r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b,A,B},x] && NonzeroQ[a*B^3-b*A^3] && NegQ[a/b]


Int[(A_+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  -C^2/b*Int[1/(B-C*x),x] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[B^2-A*C] && ZeroQ[b*B^3+a*C^3]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/b^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A*b^(2/3)-a^(1/3)*b^(1/3)*B-2*a^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/b^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[a^(1/3)*b^(1/3)*B+2*a^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/b^(1/3)},
  C/b*Int[1/(q+x),x] + C*q/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A*b^(2/3)-2*a^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/(-b)^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A*(-b)^(2/3)-(-a)^(1/3)*(-b)^(1/3)*B-2*(-a)^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/(-b)^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[(-a)^(1/3)*(-b)^(1/3)*B+2*(-a)^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/(-b)^(1/3)},
  C/b*Int[1/(q+x),x] + C*q/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A*(-b)^(2/3)-2*(-a)^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/b^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A*b^(2/3)+(-a)^(1/3)*b^(1/3)*B-2*(-a)^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/b^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[(-a)^(1/3)*b^(1/3)*B-2*(-a)^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/b^(1/3)},
  -C/b*Int[1/(q-x),x] - C*q/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A*b^(2/3)-2*(-a)^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/(-b)^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A*(-b)^(2/3)+a^(1/3)*(-b)^(1/3)*B-2*a^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/(-b)^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[a^(1/3)*(-b)^(1/3)*B-2*a^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/(-b)^(1/3)},
  -C/b*Int[1/(q-x),x] - C*q/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A*(-b)^(2/3)-2*a^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A-(a/b)^(1/3)*B-2*(a/b)^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[(a/b)^(1/3)*B+2*(a/b)^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  C/b*Int[1/(q+x),x] + C*q/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A-2*(a/b)^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[a/b,3]},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A-Rt[a/b,3]*B-2*Rt[a/b,3]^2*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[a/b,3]},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[Rt[a/b,3]*B+2*Rt[a/b,3]^2*C]


Int[(A_.+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[a/b,3]},
  C/b*Int[1/(q+x),x] + C*q/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A-2*Rt[a/b,3]^2*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A+(-a/b)^(1/3)*B-2*(-a/b)^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[(-a/b)^(1/3)*B-2*(-a/b)^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  -C/b*Int[1/(q-x),x] - C*q/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A-2*(-a/b)^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[-a/b,3]},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A+Rt[-a/b,3]*B-2*Rt[-a/b,3]^2*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[-a/b,3]},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[Rt[-a/b,3]*B-2*Rt[-a/b,3]^2*C]


Int[(A_.+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[-a/b,3]},
  -C/b*Int[1/(q-x),x] - C*q/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A-2*Rt[-a/b,3]^2*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Int[(A+B*x)/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,A,B,C},x] && (ZeroQ[a*B^3-b*A^3] || Not[RationalQ[a/b]])


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  B*Int[x/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,B,C},x] && Not[RationalQ[a/b]]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  A*Int[1/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,A,C},x] && Not[RationalQ[a,b,A,C]]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  q^2/a*Int[(A+C*q*x)/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A-B*(a/b)^(1/3)+C*(a/b)^(2/3)]


Int[x_*(B_.+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  C*q^3/a*Int[x/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[B*(a/b)^(1/3)-C*(a/b)^(2/3)]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  q^2/a*Int[(A+C*q*x)/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A+C*(a/b)^(2/3)]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  q/a*Int[(A*q+(A+B*q)*x)/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && ZeroQ[A+B*(-a/b)^(1/3)+C*(-a/b)^(2/3)]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  B*q^2/a*Int[x/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && ZeroQ[B*(-a/b)^(1/3)+C*(-a/b)^(2/3)]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  A*q/a*Int[(q+x)/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && ZeroQ[A+C*(-a/b)^(2/3)]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  q*(A-B*q+C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(2*A+B*q-C*q^2)-(A-B*q-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[A-B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b>0


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  -q*(B*q-C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(B*q-C*q^2)+(B*q+2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[B*q-C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b>0


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  q*(A+C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(2*A-C*q^2)-(A-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NonzeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b>0


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  q*(A+B*q+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(q*(2*A-B*q-C*q^2)+(A+B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[A+B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NonzeroQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b<0


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  q*(B*q+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(-q*(B*q+C*q^2)+(B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[B*q+C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b<0


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  q*(A+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(q*(2*A-C*q^2)+(A-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NonzeroQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b<0


Int[(c_.*x_)^m_.*Pq_/(a_+b_.*x_^n_),x_Symbol] :=
  With[{v=Sum[(c*x)^(m+ii)*(Coeff[Pq,x,ii]+Coeff[Pq,x,n/2+ii]*x^(n/2))/(c^ii*(a+b*x^n)),{ii,0,n/2-1}]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && PositiveIntegerQ[n/2] && Expon[Pq,x]<n


Int[Pq_/(a_+b_.*x_^n_),x_Symbol] :=
  With[{v=Sum[x^ii*(Coeff[Pq,x,ii]+Coeff[Pq,x,n/2+ii]*x^(n/2))/(a+b*x^n),{ii,0,n/2-1}]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n/2] && Expon[Pq,x]<n


(* Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  Sqrt[c+d*x]*Sqrt[c^2-c*d*x+d^2*x^2]/Sqrt[a+b*x^3]*Int[Sqrt[c+d*x]/Sqrt[c^2-c*d*x+d^2*x^2],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c^3-a*d^3] *)


Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  -d*Sqrt[18-6*I*Sqrt[3]]*Sqrt[1+Rt[b/a,3]*x]*Sqrt[(I+Sqrt[3])/(3*I+Sqrt[3])-2*Rt[b/a,3]*x/(3-I*Sqrt[3])]*
    Sqrt[(I-Sqrt[3])/(3*I-Sqrt[3])-2*Rt[b/a,3]*x/(3+I*Sqrt[3])]/
    (Rt[b/a,3]^2*Sqrt[a+b*x^3])*
    EllipticE[ArcSin[Sqrt[2]*Sqrt[1+Rt[b/a,3]*x]/Sqrt[3+I*Sqrt[3]]],(3*I-Sqrt[3])/(3*I+Sqrt[3])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[2*Rt[b/a,3]*c+(1-I*Sqrt[3])*d]


Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  -d*Sqrt[18-6*I*Sqrt[3]]*Sqrt[1+(b/a)^(1/3)*x]*Sqrt[(I+Sqrt[3])/(3*I+Sqrt[3])-2*(b/a)^(1/3)*x/(3-I*Sqrt[3])]*
    Sqrt[(I-Sqrt[3])/(3*I-Sqrt[3])-2*(b/a)^(1/3)*x/(3+I*Sqrt[3])]/
    ((b/a)^(2/3)*Sqrt[a+b*x^3])*
    EllipticE[ArcSin[Sqrt[2]*Sqrt[1+(b/a)^(1/3)*x]/Sqrt[3+I*Sqrt[3]]],(3*I-Sqrt[3])/(3*I+Sqrt[3])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[2*(b/a)^(1/3)*c+(1-I*Sqrt[3])*d]


Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  (2*Rt[b/a,3]*c+(1-I*Sqrt[3])*d)/(2*Rt[b/a,3])*Int[1/Sqrt[a+b*x^3],x] - 
  d/(2*Rt[b/a,3])*Int[(1-I*Sqrt[3]-2*Rt[b/a,3]*x)/Sqrt[a+b*x^3],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[2*Rt[b/a,3]*c+(1-I*Sqrt[3])*d]


Int[(c_+d_.*x_^4)/Sqrt[a_+b_.*x_^6],x_Symbol] :=
  (1+Sqrt[3])*d*x*Sqrt[a+b*x^6]/(2*a*Rt[b/a,3]^2*(1+(1+Sqrt[3])*Rt[b/a,3]*x^2)) - 
  ((3^(1/4)*d*x*(1+Rt[b/a,3]*x^2)*Sqrt[(1-Rt[b/a,3]*x^2+Rt[b/a,3]^2*x^4)/(1+(1+Sqrt[3])*Rt[b/a,3]*x^2)^2])/
    (2*Rt[b/a,3]^2*Sqrt[Rt[b/a,3]*x^2*(1+Rt[b/a,3]*x^2)/(1+(1+Sqrt[3])*Rt[b/a,3]*x^2)^2]*Sqrt[a+b*x^6]))*
    EllipticE[ArcCos[(1+(1-Sqrt[3])*Rt[b/a,3]*x^2)/(1+(1+Sqrt[3])*Rt[b/a,3]*x^2)],(2+Sqrt[3])/4] /;
FreeQ[{a,b,c,d},x] && ZeroQ[2*Rt[b/a,3]^2*c-(1-Sqrt[3])*d]


Int[(c_+d_.*x_^4)/Sqrt[a_+b_.*x_^6],x_Symbol] :=
  (2*Rt[b/a,3]^2*c-(1-Sqrt[3])*d)/(2*Rt[b/a,3]^2)*Int[1/Sqrt[a+b*x^6],x] + 
  d/(2*Rt[b/a,3]^2)*Int[(1-Sqrt[3]+2*Rt[b/a,3]^2*x^4)/Sqrt[a+b*x^6],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[2*Rt[b/a,3]^2*c-(1-Sqrt[3])*d]


Int[(c_+d_.*x_^2)/Sqrt[a_+b_.*x_^8],x_Symbol] :=
  -c*d*x^3*Sqrt[-(c-d*x^2)^2/(c*d*x^2)]*Sqrt[-d^2*(a+b*x^8)/(b*c^2*x^4)]/(Sqrt[2+Sqrt[2]]*(c-d*x^2)*Sqrt[a+b*x^8])*
    EllipticF[ArcSin[1/2*Sqrt[(Sqrt[2]*c^2+2*c*d*x^2+Sqrt[2]*d^2*x^4)/(c*d*x^2)]],-2*(1-Sqrt[2])] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c^4-a*d^4]


Int[(c_+d_.*x_^2)/Sqrt[a_+b_.*x_^8],x_Symbol] :=
  (d+Rt[b/a,4]*c)/(2*Rt[b/a,4])*Int[(1+Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] - 
  (d-Rt[b/a,4]*c)/(2*Rt[b/a,4])*Int[(1-Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c^4-a*d^4]


Int[Pq_/(x_*Sqrt[a_+b_.*x_^n_]),x_Symbol] :=
  Coeff[Pq,x,0]*Int[1/(x*Sqrt[a+b*x^n]),x] + 
  Int[ExpandToSum[(Pq-Coeff[Pq,x,0])/x,x]/Sqrt[a+b*x^n],x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && NonzeroQ[Coeff[Pq,x,0]]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],j,k},
  Int[Sum[(c*x)^(m+j)/c^j*Sum[Coeff[Pq,x,j+k*n/2]*x^(k*n/2),{k,0,2*(q-j)/n+1}]*(a+b*x^n)^p,{j,0,n/2-1}],x]] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n/2] && Not[PolyQ[Pq,x^(n/2)]]


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],j,k},
  Int[Sum[x^j*Sum[Coeff[Pq,x,j+k*n/2]*x^(k*n/2),{k,0,2*(q-j)/n+1}]*(a+b*x^n)^p,{j,0,n/2-1}],x]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n/2] && Not[PolyQ[Pq,x^(n/2)]]


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Coeff[Pq,x,n-1]*Int[x^(n-1)*(a+b*x^n)^p,x] + 
  Int[ExpandToSum[Pq-Coeff[Pq,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && Expon[Pq,x]==n-1


Int[(c_.*x_)^m_.*Pq_/(a_+b_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq/(a+b*x^n),x],x] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && IntegerQ[n]


Int[Pq_/(a_+b_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[Pq/(a+b*x^n),x],x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && IntegerQ[n]


Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{Pq0=Coeff[Pq,x,0]},
    Pq0*(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) + 
    1/(2*a*c*(m+1))*Int[(c*x)^(m+1)*ExpandToSum[2*a*(m+1)*(Pq-Pq0)/x-2*b*Pq0*(m+n*(p+1)+1)*x^(n-1),x]*(a+b*x^n)^p,x] /;
 NonzeroQ[Pq0]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && n-1<=Expon[Pq,x]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*(c*x)^(m+q-n+1)*(a+b*x^n)^(p+1)/(b*c^(q-n+1)*(m+q+n*p+1)) + 
    1/(b*(m+q+n*p+1))*Int[(c*x)^m*ExpandToSum[b*(m+q+n*p+1)*(Pq-Pqq*x^q)-a*Pqq*(m+q-n+1)*x^(q-n),x]*(a+b*x^n)^p,x]] /;
  NonzeroQ[m+q+n*p+1] && q-n>=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n]


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*x^(q-n+1)*(a+b*x^n)^(p+1)/(b*(q+n*p+1)) + 
    1/(b*(q+n*p+1))*Int[ExpandToSum[b*(q+n*p+1)*(Pq-Pqq*x^q)-a*Pqq*(q-n+1)*x^(q-n),x]*(a+b*x^n)^p,x]] /;
  NonzeroQ[q+n*p+1] && q-n>=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  -Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n))^p/x^(m+q+2),x],x,1/x]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=Denominator[m],q=Expon[Pq,x]},
  -g/c*Subst[Int[ExpandToSum[x^(g*q)*ReplaceAll[Pq,x->c^(-1)*x^(-g)],x]*
    (a+b*c^(-n)*x^(-g*n))^p/x^(g*(m+q+1)+1),x],x,1/(c*x)^(1/g)]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && NegativeIntegerQ[n] && FractionQ[m]


Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  -(c*x)^m*(x^(-1))^m*Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n))^p/x^(m+q+2),x],x,1/x]] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,m,p},x] && PolyQ[Pq,x] && FractionQ[n]


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && FractionQ[n]


Int[(c_*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*Pq*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && FractionQ[n]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[ReplaceAll[SubstFor[x^n,Pq,x],x->x^Simplify[n/(m+1)]]*(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*Pq*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(A_+B_.*x_^m_)*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  A*Int[(a+b*x^n)^p,x] +
  B*Int[x^(n-1)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,A,B,m,n,p},x] && ZeroQ[m-n+1]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,m,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])


Int[Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])


Int[u_^m_.*Pq_*(a_+b_.*v_^n_.)^p_,x_Symbol] :=
  u^m/(Coeff[v,x,1]*v^m)*Subst[Int[x^m*SubstFor[v,Pq,x]*(a+b*x^n)^p,x],x,v] /;
FreeQ[{a,b,m,n,p},x] && LinearPairQ[u,v,x] && PolyQ[Pq,v^n]


Int[Pq_*(a_+b_.*v_^n_.)^p_,x_Symbol] :=
  1/Coeff[v,x,1]*Subst[Int[SubstFor[v,Pq,x]*(a+b*x^n)^p,x],x,v] /;
FreeQ[{a,b,n,p},x] && LinearQ[v,x] && PolyQ[Pq,v^n]


Int[Px_^q_.*(a_.+b_.*(c_+d_.*x_)^n_)^p_,x_Symbol] :=
  With[{k=Denominator[n]},
  k/d*Subst[Int[SimplifyIntegrand[x^(k-1)*ReplaceAll[Px,x->x^k/d-c/d]^q*(a+b*x^(k*n))^p,x],x],x,(c+d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && PolynomialQ[Px,x] && IntegerQ[q] && RationalQ[n]





(* ::Subsection::Closed:: *)
(*4.5 (d x)^m Pq(x) (a+b x^n+c x^(2 n))^p*)


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[SubstFor[x^n,Pq,x]*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && ZeroQ[Simplify[m-n+1]]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && PositiveIntegerQ[p]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && PositiveIntegerQ[p]


Int[(d_+e_.*x_^n_.+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*x*(a+b*x^n+c*x^(2*n))^(p+1)/a /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[a*e-b*d*(n+n*p+1)] && ZeroQ[a*f-c*d*(2*n*(p+1)+1)]


Int[(d_+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*x*(a+b*x^n+c*x^(2*n))^(p+1)/a /;
FreeQ[{a,b,c,d,f,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[n+n*p+1] && ZeroQ[c*d+a*f]


Int[(g_.*x_)^m_.*(d_+e_.*x_^n_.+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*(g*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*g*(m+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[a*e*(m+1)-b*d*(m+n+n*p+1)] && ZeroQ[a*f*(m+1)-c*d*(m+2*n*(p+1)+1)] && 
  NonzeroQ[m+1]


Int[(g_.*x_)^m_.*(d_+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*(g*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*g*(m+1)) /;
FreeQ[{a,b,c,d,f,g,m,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[m+n+n*p+1] && ZeroQ[c*d+a*f] && NonzeroQ[m+1]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p]))*Int[(d*x)^m*Pq*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,m,n,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[2*p]]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p]))*Int[Pq*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[2*p]]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Pq,x]*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[(d_*x_)^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^m/x^m*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/d*Int[(d*x)^(m+1)*ExpandToSum[Pq/x,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && ZeroQ[Coeff[Pq,x,0]]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[x*ExpandToSum[Pq/x,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && ZeroQ[Coeff[Pq,x,0]] && SumQ[Pq]


Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],i},
  -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c))*
    Sum[((b^2-2*a*c)*Coeff[Pq,x,i]-a*b*Coeff[Pq,x,n+i])*x^i+
      c*(b*Coeff[Pq,x,i]-2*a*Coeff[Pq,x,n+i])*x^(n+i),{i,0,n-1}] + 
  1/(a*n*(p+1)*(b^2-4*a*c))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*
    Sum[((b^2*(n*(p+1)+i+1)-2*a*c*(2*n*(p+1)+i+1))*Coeff[Pq,x,i]-a*b*(i+1)*Coeff[Pq,x,n+i])*x^i+
      c*(n*(2*p+3)+i+1)*(b*Coeff[Pq,x,i]-2*a*Coeff[Pq,x,n+i])*x^(n+i),{i,0,n-1}],x] /;
 q<2*n] /;
FreeQ[{a,b,c},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Module[{Q=PolynomialQuotient[(b*c)^(Floor[(q-1)/n]+1)*Pq,a+b*x^n+c*x^(2*n),x],
          R=PolynomialRemainder[(b*c)^(Floor[(q-1)/n]+1)*Pq,a+b*x^n+c*x^(2*n),x],i},
  -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*
    Sum[((b^2-2*a*c)*Coeff[R,x,i]-a*b*Coeff[R,x,n+i])*x^i+
      c*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}] + 
  1/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*ExpandToSum[a*n*(p+1)*(b^2-4*a*c)*Q+
    Sum[((b^2*(n*(p+1)+i+1)-2*a*c*(2*n*(p+1)+i+1))*Coeff[R,x,i]-a*b*(i+1)*Coeff[R,x,n+i])*x^i+
     c*(n*(2*p+3)+i+1)*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}],x],x]] /;
 q>=2*n] /;
FreeQ[{a,b,c},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[x_^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x]},
  Module[{Q=PolynomialQuotient[a*(b*c)^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n+c*x^(2*n),x],
          R=PolynomialRemainder[a*(b*c)^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n+c*x^(2*n),x],i},
  -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*
    Sum[((b^2-2*a*c)*Coeff[R,x,i]-a*b*Coeff[R,x,n+i])*x^i+
      c*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}] + 
  1/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*Int[x^m*(a+b*x^n+c*x^(2*n))^(p+1)*
    ExpandToSum[n*(p+1)*(b^2-4*a*c)*x^(-m)*Q+
      Sum[((b^2*(n*(p+1)+i+1)/a-2*c*(2*n*(p+1)+i+1))*Coeff[R,x,i]-b*(i+1)*Coeff[R,x,n+i])*x^(i-m)+
       c*(n*(2*p+3)+i+1)*(b/a*Coeff[R,x,i]-2*Coeff[R,x,n+i])*x^(n+i-m),{i,0,n-1}],x],x]] /;
 q>=2*n] /;
FreeQ[{a,b,c},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[p] && p<-1 && NegativeIntegerQ[m]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  With[{g=GCD[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*ReplaceAll[Pq,x->x^(1/g)]*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g] /;
 g!=1] /;
FreeQ[{a,b,c,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_.*Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && NiceSqrtQ[b^2-4*a*c]


Int[Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  (NiceSqrtQ[b^2-4*a*c] || Expon[Pq,x]<n)


Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    c^p*Pqq*Log[a+b*x+c*x^2]/2 + 
    1/2*Int[ExpandToSum[2*Pq-c^p*Pqq*(b+2*c*x)/(a+b*x+c*x^2)^(p+1),x]*(a+b*x+c*x^2)^p,x]] /;
  q+2*p+1==0] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p]


Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    c^p*Pqq*ArcTanh[(b+2*c*x)/(2*Rt[c,2]*Sqrt[a+b*x+c*x^2])] + 
    Int[ExpandToSum[Pq-c^(p+1/2)*Pqq/(a+b*x+c*x^2)^(p+1/2),x]*(a+b*x+c*x^2)^p,x]] /;
  q+2*p+1==0] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1/2] && PosQ[c]


Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    -(-c)^p*Pqq*ArcTan[(b+2*c*x)/(2*Rt[-c,2]*Sqrt[a+b*x+c*x^2])] + 
    Int[ExpandToSum[Pq-(-c)^(p+1/2)*Pqq/(a+b*x+c*x^2)^(p+1/2),x]*(a+b*x+c*x^2)^p,x]] /;
  q+2*p+1==0] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1/2] && NegQ[c]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*(d*x)^(m+q-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*d^(q-2*n+1)*(m+q+2*n*p+1)) + 
    Int[(d*x)^m*ExpandToSum[Pq-Pqq*x^q-Pqq*(a*(m+q-2*n+1)*x^(q-2*n)+b*(m+q+n*(p-1)+1)*x^(q-n))/(c*(m+q+2*n*p+1)),x]*
      (a+b*x^n+c*x^(2*n))^p,x]] /;
  q>=2*n && m+q+2*n*p+1!=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,c,d,m,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*x^(q-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(q+2*n*p+1)) + 
    Int[ExpandToSum[Pq-Pqq*x^q-Pqq*(a*(q-2*n+1)*x^(q-2*n)+b*(q+n*(p-1)+1)*x^(q-n))/(c*(q+2*n*p+1)),x]*(a+b*x^n+c*x^(2*n))^p,x]] /;
  q>=2*n && q+2*n*p+1!=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,c,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],j,k},
  Int[Sum[1/d^j*(d*x)^(m+j)*Sum[Coeff[Pq,x,j+k*n]*x^(k*n),{k,0,(q-j)/n+1}]*(a+b*x^n+c*x^(2*n))^p,{j,0,n-1}],x]] /;
FreeQ[{a,b,c,d,m,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[PolyQ[Pq,x^n]]


Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],j,k},
  Int[Sum[x^j*Sum[Coeff[Pq,x,j+k*n]*x^(k*n),{k,0,(q-j)/n+1}]*(a+b*x^n+c*x^(2*n))^p,{j,0,n-1}],x]] /;
FreeQ[{a,b,c,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[PolyQ[Pq,x^n]]


Int[(d_.*x_)^m_.*Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
  Int[RationalFunctionExpand[(d*x)^m*Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
  Int[RationalFunctionExpand[Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  -Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+q+2),x],x,1/x]] /;
FreeQ[{a,b,c,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[m],q=Expon[Pq,x]},
  -g/d*Subst[Int[ExpandToSum[x^(g*q)*ReplaceAll[Pq,x->d^(-1)*x^(-g)],x]*
    (a+b*d^(-n)*x^(-g*n)+c*d^(-2*n)*x^(-2*g*n))^p/x^(g*(m+q+1)+1),x],x,1/(d*x)^(1/g)]] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && FractionQ[m]


Int[(d_.*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  -(d*x)^m*(x^(-1))^m*Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+q+2),x],x,1/x]] /;
FreeQ[{a,b,c,d,m,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,m,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && FractionQ[n]


Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && FractionQ[n]


Int[(d_*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(m-1/2)*Sqrt[d*x]/Sqrt[x]*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && FractionQ[n] && PositiveIntegerQ[m+1/2]


Int[(d_*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(m+1/2)*Sqrt[x]/Sqrt[d*x]*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && FractionQ[n] && NegativeIntegerQ[m-1/2]


Int[(d_*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^m/x^m*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c] && FractionQ[n]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[ReplaceAll[SubstFor[x^n,Pq,x],x->x^Simplify[n/(m+1)]]*(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && 
  Not[IntegerQ[n]]


Int[(d_*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^m/x^m*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,p},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x^n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && 
  Not[IntegerQ[n]]


Int[(d_.*x_)^m_.*Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[(d*x)^m*Pq/(b-q+2*c*x^n),x] -
  2*c/q*Int[(d*x)^m*Pq/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c]


Int[Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[Pq/(b-q+2*c*x^n),x] -
  2*c/q*Int[Pq/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NonzeroQ[b^2-4*a*c]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NegativeIntegerQ[p+1]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && PolyQ[Pq,x] && NegativeIntegerQ[p+1]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Defer[Int][(d*x)^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && ZeroQ[n2-2*n] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Defer[Int][Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n2-2*n] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])


Int[u_^m_.*Pq_*(a_+b_.*v_^n_+c_.*w_^n2_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*SubstFor[v,Pq,x]*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[n2-2*n] && LinearPairQ[u,v,x] && ZeroQ[v-w] && PolyQ[Pq,v^n]


Int[Pq_*(a_+b_.*v_^n_+c_.*w_^n2_.)^p_.,x_Symbol] :=
  1/Coefficient[v,x,1]*Subst[Int[SubstFor[v,Pq,x]*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n2-2*n] && LinearQ[v,x] && ZeroQ[v-w] && PolyQ[Pq,v^n]





(* ::Subsection::Closed:: *)
(*3.8 (a x^j+b x^n)^p*)


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(b*(n-j)(p+1)*x^(n-1)) /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && ZeroQ[j*p-n+j+1]


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) + 
  (n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
FreeQ[{a,b,j,n},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && NegativeIntegerQ[Simplify[(n*p+n-j+1)/(n-j)]] && RationalQ[p] && p<-1


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(a*(j*p+1)*x^(j-1)) - 
  b*(n*p+n-j+1)/(a*(j*p+1))*Int[x^(n-j)*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && NegativeIntegerQ[Simplify[(n*p+n-j+1)/(n-j)]] && NonzeroQ[j*p+1]


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/(j*p+1) - 
  b*(n-j)*p/(j*p+1)*Int[x^n*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && p>0 && j*p+1<0


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/(n*p+1) + 
  a*(n-j)*p/(n*p+1)*Int[x^j*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && p>0 && NonzeroQ[n*p+1]


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(b*(n-j)*(p+1)*x^(n-1)) - 
  (j*p-n+j+1)/(b*(n-j)*(p+1))*Int[(a*x^j+b*x^n)^(p+1)/x^n,x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && p<-1 && j*p+1>n-j


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) + 
  (n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && p<-1


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/(p*(n-j)) + a*Int[x^j*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b,j,n},x] && PositiveIntegerQ[p+1/2] && NonzeroQ[n-j] && ZeroQ[Simplify[j*p+1]]


Int[1/Sqrt[a_.*x_^2+b_.*x_^n_.],x_Symbol] :=
  2/(2-n)*Subst[Int[1/(1-a*x^2),x],x,x/Sqrt[a*x^2+b*x^n]] /;
FreeQ[{a,b,n},x] && NonzeroQ[n-2]


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) + 
  (n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
FreeQ[{a,b,j,n},x] && NegativeIntegerQ[p+1/2] && NonzeroQ[n-j] && ZeroQ[Simplify[j*p+1]]


Int[1/Sqrt[a_.*x_^j_.+b_.*x_^n_.],x_Symbol] :=
  -2*Sqrt[a*x^j+b*x^n]/(b*(n-2)*x^(n-1)) - 
  a*(2*n-j-2)/(b*(n-2))*Int[1/(x^(n-j)*Sqrt[a*x^j+b*x^n]),x] /;
FreeQ[{a,b},x] && RationalQ[j,n] && 2*(n-1)<j<n


(* Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/(p*(n-j)*((a*x^j+b*x^n)/(b*x^n))^p)*Hypergeometric2F1[-p,-p,1-p,-a/(b*x^(n-j))] /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && ZeroQ[j*p+1] *)


(* Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/((j*p+1)*((a*x^j+b*x^n)/(a*x^j))^p)*
    Hypergeometric2F1[-p,(j*p+1)/(n-j),(j*p+1)/(n-j)+1,-b*x^(n-j)/a] /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && NonzeroQ[j*p+1] *)


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^FracPart[p]/(x^(j*FracPart[p])*(a+b*x^(n-j))^FracPart[p])*Int[x^(j*p)*(a+b*x^(n-j))^p,x] /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && PosQ[n-j]


Int[(a_.*u_^j_.+b_.*v_^n_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a*x^j+b*x^n)^p,x],x,u] /;
FreeQ[{a,b,j,n,p},x] && ZeroQ[u-v] && LinearQ[u,x] && NonzeroQ[u-x]


(* ::Subsection::Closed:: *)
(*3.9 (c x)^m (a x^j+b x^n)^p*)


Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && ZeroQ[Simplify[m-n+1]]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && ZeroQ[m+n*p+n-j+1] && (IntegerQ[j] || PositiveQ[c])


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) + 
  c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,j,m,n},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && NegativeIntegerQ[Simplify[(m+n*p+n-j+1)/(n-j)]] && 
  RationalQ[p] && p<-1 && (IntegerQ[j] || PositiveQ[c])


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(m+j*p+1)) - 
  b*(m+n*p+n-j+1)/(a*c^(n-j)*(m+j*p+1))*Int[(c*x)^(m+n-j)*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && NegativeIntegerQ[Simplify[(m+n*p+n-j+1)/(n-j)]] && 
  NonzeroQ[m+j*p+1] && (IntegersQ[j,n] || PositiveQ[c])


Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && NegativeIntegerQ[Simplify[(m+n*p+n-j+1)/(n-j)]]


Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[(m+1)/n]] && 
  NonzeroQ[n^2-1]


Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[(m+1)/n]] && 
  NonzeroQ[n^2-1]


Int[(c_.*x_)^m_*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*(m+j*p+1)) - 
  b*p*(n-j)/(c^n*(m+j*p+1))*Int[(c*x)^(m+n)*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[p]] && RationalQ[j,m,n,p] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && p>0 && m+j*p+1<0


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*(m+n*p+1)) + 
  a*(n-j)*p/(c^j*(m+n*p+1))*Int[(c*x)^(m+j)*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && p>0 && NonzeroQ[m+n*p+1]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a*x^j+b*x^n)^(p+1)/(b*(n-j)*(p+1)) - 
  c^n*(m+j*p-n+j+1)/(b*(n-j)*(p+1))*Int[(c*x)^(m-n)*(a*x^j+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[p]] && RationalQ[j,m,n,p] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && p<-1 && m+j*p+1>n-j


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) + 
  c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && p<-1


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a*x^j+b*x^n)^(p+1)/(b*(m+n*p+1)) - 
  a*c^(n-j)*(m+j*p-n+j+1)/(b*(m+n*p+1))*Int[(c*x)^(m-(n-j))*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && Not[IntegerQ[p]] && RationalQ[j,n] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && PositiveQ[m+j*p+1-n+j] && 
  NonzeroQ[m+n*p+1]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(m+j*p+1)) - 
  b*(m+n*p+n-j+1)/(a*c^(n-j)*(m+j*p+1))*Int[(c*x)^(m+n-j)*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && Not[IntegerQ[p]] && RationalQ[j,n] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && NegativeQ[m+j*p+1]


Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a*x^Simplify[j/(m+1)]+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && NonzeroQ[m+1] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && NonzeroQ[m+1] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*p*(n-j)) + a/c^j*Int[(c*x)^(m+j)*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c,j,m,n},x] && PositiveIntegerQ[p+1/2] && NonzeroQ[n-j] && ZeroQ[Simplify[m+j*p+1]] && (IntegerQ[j] || PositiveQ[c])


Int[x_^m_./Sqrt[a_.*x_^j_.+b_.*x_^n_.],x_Symbol] :=
  -2/(n-j)*Subst[Int[1/(1-a*x^2),x],x,x^(j/2)/Sqrt[a*x^j+b*x^n]] /;
FreeQ[{a,b,j,n},x] && ZeroQ[m-j/2+1] && NonzeroQ[n-j]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) + 
  c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,j,m,n},x] && NegativeIntegerQ[p+1/2] && NonzeroQ[n-j] && ZeroQ[Simplify[m+j*p+1]] && (IntegerQ[j] || PositiveQ[c])


Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && IntegerQ[p+1/2] && NonzeroQ[n-j] && ZeroQ[Simplify[m+j*p+1]]


(* Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(b*p*(n-j)*x^(n+j*p))*Hypergeometric2F1[1,1,1-p,-a/(b*x^(n-j))] /;
FreeQ[{a,b,j,m,n,p},x] && NonzeroQ[n-j] && ZeroQ[m+j*p+1] *)


(* Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(b*(p-1)*(n-j)*x^(2*n+j*(p-1)))*Hypergeometric2F1[1,2,2-p,-a/(b*x^(n-j))] /;
FreeQ[{a,b,j,m,n,p},x] && NonzeroQ[n-j] && ZeroQ[m+n+(p-1)*j+1] *)


(* Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (x^(m-j+1)*(a*x^j+b*x^n)^(p+1))/(a*(m+j*p+1))*Hypergeometric2F1[1,(m+n*p+1)/(n-j)+1,(m+j*p+1)/(n-j)+1,-b*x^(n-j)/a] /;
FreeQ[{a,b,j,m,n,p},x] && NonzeroQ[n-j] && NonzeroQ[m+j*p+1] && NonzeroQ[m+n+(p-1)*j+1] *)


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]*(a*x^j+b*x^n)^FracPart[p]/
    (x^(FracPart[m]+j*FracPart[p])*(a+b*x^(n-j))^FracPart[p])*
    Int[x^(m+j*p)*(a+b*x^(n-j))^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NonzeroQ[n-j] && PosQ[n-j]


Int[u_^m_.*(a_.*v_^j_.+b_.*w_^n_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a*x^j+b*x^n)^p,x],x,v] /;
FreeQ[{a,b,j,m,n,p},x] && LinearPairQ[u,v,x] && ZeroQ[v-w]


(* ::Subsection::Closed:: *)
(*3.10 (e x)^m (a x^j+b x^k)^p (c+d x^n)^q*)


Int[x_^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a*x^Simplify[j/n]+b*x^Simplify[k/n])^p*(c+d*x)^q,x],x,x^n] /;
FreeQ[{a,b,c,d,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[k-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] && 
  IntegerQ[Simplify[(m+1)/n]] && NonzeroQ[n^2-1]


Int[(e_*x_)^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^k)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[k-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] && 
  IntegerQ[Simplify[(m+1)/n]] && NonzeroQ[n^2-1]


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
  c*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*(m+j*p+1)) /;
FreeQ[{a,b,c,d,e,j,m,n,p},x] && ZeroQ[jn-j-n] && Not[IntegerQ[p]] && NonzeroQ[b*c-a*d] && 
  ZeroQ[a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1)] && (PositiveQ[e] || IntegersQ[j]) && NonzeroQ[m+j*p+1]


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
  -e^(j-1)*(b*c-a*d)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*b*n*(p+1)) - 
  e^j*(a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(a*b*n*(p+1))*Int[(e*x)^(m-j)*(a*x^j+b*x^(j+n))^(p+1),x] /;
FreeQ[{a,b,c,d,e,j,m,n},x] && ZeroQ[jn-j-n] && Not[IntegerQ[p]] && NonzeroQ[b*c-a*d] && RationalQ[j,m,p] && p<-1 && 0<j<=m && 
  (PositiveQ[e] || IntegerQ[j])


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
  c*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*(m+j*p+1)) + 
  (a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(a*e^n*(m+j*p+1))*Int[(e*x)^(m+n)*(a*x^j+b*x^(j+n))^p,x] /;
FreeQ[{a,b,c,d,e,j,p},x] && ZeroQ[jn-j-n] && Not[IntegerQ[p]] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && n>0 && 
  (m+j*p<-1 || IntegersQ[m-1/2,p-1/2] && p<0 && m<-n*p-1) && 
  (PositiveQ[e] || IntegersQ[j,n]) && NonzeroQ[m+j*p+1] && NonzeroQ[m-n+j*p+1]


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
  d*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(b*(m+n+p*(j+n)+1)) - 
  (a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(b*(m+n+p*(j+n)+1))*Int[(e*x)^m*(a*x^j+b*x^(j+n))^p,x] /;
FreeQ[{a,b,c,d,e,j,m,n,p},x] && ZeroQ[jn-j-n] && Not[IntegerQ[p]] && NonzeroQ[b*c-a*d] && 
  NonzeroQ[m+n+p*(j+n)+1] && (PositiveQ[e] || IntegerQ[j])


Int[x_^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a*x^Simplify[j/(m+1)]+b*x^Simplify[k/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[k-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] && 
  NonzeroQ[m+1] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_*x_)^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^k)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[k-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] && 
  NonzeroQ[m+1] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]*(a*x^j+b*x^(j+n))^FracPart[p]/
    (x^(FracPart[m]+j*FracPart[p])*(a+b*x^n)^FracPart[p])*
    Int[x^(m+j*p)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,j,m,n,p,q},x] && ZeroQ[jn-j-n] && Not[IntegerQ[p]] && NonzeroQ[b*c-a*d] && Not[ZeroQ[n-1] && ZeroQ[j-1]]


(* ::Subsection::Closed:: *)
(*3.11 (c x)^m Pq(x) (a x^j+b x^n)^p*)


Int[Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  With[{d=Denominator[n]},
  d*Subst[Int[x^(d-1)*ReplaceAll[SubstFor[x^n,Pq,x],x->x^(d*n)]*(a*x^(d*j)+b*x^(d*n))^p,x],x,x^(1/d)]] /;
FreeQ[{a,b,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NonzeroQ[n-j] && RationalQ[j,n] && IntegerQ[j/n] && -1<n<1


Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Pq,x]*(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[(m+1)/n]]


Int[(c_*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^(Sign[m]*Quotient[m,Sign[m]])*(c*x)^Mod[m,Sign[m]]/x^Mod[m,Sign[m]]*Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[(m+1)/n]] && RationalQ[m] && m^2>1


Int[(c_*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=GCD[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*ReplaceAll[Pq,x->x^(1/g)]*(a*x^(j/g)+b*x^(n/g))^p,x],x,x^g] /;
 g!=1] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && PositiveIntegerQ[j,n,j/n] && IntegerQ[m]


Int[(c_.*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*(c*x)^(m+q-n+1)*(a*x^j+b*x^n)^(p+1)/(b*c^(q-n+1)*(m+q+n*p+1)) + 
    Int[(c*x)^m*ExpandToSum[Pq-Pqq*x^q-a*Pqq*(m+q-n+1)*x^(q-n)/(b*(m+q+n*p+1)),x]*(a*x^j+b*x^n)^p,x]] /;
  q>n-1 && m+q+n*p+1!=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && Not[IntegerQ[p]] && PositiveIntegerQ[j,n] && j<n


Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[
    Int[ReplaceAll[SubstFor[x^n,Pq,x],x->x^Simplify[n/(m+1)]]*(a*x^Simplify[j/(m+1)]+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_*x_)^m_*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^(Sign[m]*Quotient[m,Sign[m]])*(c*x)^Mod[m,Sign[m]]/x^Mod[m,Sign[m]]*Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]] && RationalQ[m] && m^2>1


Int[(c_*x_)^m_*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NonzeroQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_.*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq*(a*x^j+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,j,m,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n]) && Not[IntegerQ[p]] && NonzeroQ[n-j]


Int[Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a*x^j+b*x^n)^p,x],x] /;
FreeQ[{a,b,j,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n]) && Not[IntegerQ[p]] && NonzeroQ[n-j]





(* ::Subsection::Closed:: *)
(*5.1 u (a+b x+c x^2+d x^3)^p*)


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*a^(2*p))*Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d},x] && IntegerQ[p] && ZeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+b*x+d*x^3)^p,x],x] /;
FreeQ[{a,b,d},x] && PositiveIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+b*x+d*x^3]},
  FreeFactors[u,x]^p*Int[DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p))*Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && ZeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+b*x+d*x^3],x]},
  (a+b*x+d*x^3)^p/DistributeDegree[u,p]*Int[DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  (a+b*x+d*x^3)^p/(((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p)*
    Int[((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*a^(2*p))*Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,e,f,m},x] && IntegerQ[p] && ZeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+b*x+d*x^3)^p,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+b*x+d*x^3]},
  FreeFactors[u,x]^p*Int[(e+f*x)^m*DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p))*Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+b*x+d*x^3],x]},
  (a+b*x+d*x^3)^p/DistributeDegree[u,p]*Int[(e+f*x)^m*DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
  (a+b*x+d*x^3)^p/(((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p)*
    Int[(e+f*x)^m*((6*b*d-2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      ((6*(1+I*Sqrt[3])*b*d-2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p*
      ((6*(1-I*Sqrt[3])*b*d-2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)-3*d*x)^p,x]] /;
FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*b^3+27*a^2*d]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  -1/(3^(3*p)*d^(2*p))*Int[(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d},x] && IntegerQ[p] && ZeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+c*x^2+d*x^3]},
  FreeFactors[u,x]^p*Int[DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+c*x^2+d*x^3)^p/((c-3*d*x)^p*(2*c+3*d*x)^(2*p))*Int[(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+c*x^2+d*x^3],x]},
  (a+c*x^2+d*x^3)^p/DistributeDegree[u,p]*Int[DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  (a+c*x^2+d*x^3)^p/((c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  -1/(3^(3*p)*d^(2*p))*Int[(e+f*x)^m*(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+c*x^2+d*x^3]},
  FreeFactors[u,x]^p*Int[(e+f*x)^m*DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+c*x^2+d*x^3)^p/((c-3*d*x)^p*(2*c+3*d*x)^(2*p))*Int[(e+f*x)^m*(c-3*d*x)^p*(2*c+3*d*x)^(2*p),x] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+c*x^2+d*x^3],x]},
  (a+c*x^2+d*x^3)^p/DistributeDegree[u,p]*Int[(e+f*x)^m*DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3-27*a*d^2+3*Sqrt[3]*d*Sqrt[4*a*c^3+27*a^2*d^2],3]},
  (a+c*x^2+d*x^3)^p/((c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(e+f*x)^m*(c-(2*c^2+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2+2^(1/3)*(1-I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2+2^(1/3)*(1+I*Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[4*c^3+27*a*d^2]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Int[(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Subst[Int[(3*a*b*c-b^3+c^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[b^3-3*a*b*c,3]},
  1/(3^p*b^p*c^p)*Int[(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[c^3-3*b*c*d,3]},
  1/(3^p*b^p*c^p)*Int[(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandToSum[(a+b*x+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+b*x+c*x^2+d*x^3]},
  FreeFactors[u,x]^p*Int[DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+c*x^2+d*x^3)^p/(b+c*x)^(3*p)*Int[(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[b^3-3*a*b*c,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p)*
    Int[(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[c^3-3*b*c*d,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p)*
    Int[(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+b*x+c*x^2+d*x^3],x]},
  (a+b*x+c*x^2+d*x^3)^p/DistributeDegree[u,p]*Int[DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] *)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  (a+b*x+c*x^2+d*x^3)^p/
    ((c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && PolyQ[u,x,3] && Not[CubicMatchQ[u,x]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[b^3-3*a*b*c,3]},
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[c^3-3*b*c*d,3]},
  1/(3^p*b^p*c^p)*Int[(e+f*x)^m*(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[p] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^m*(a+b*x+c*x^2+d*x^3)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=Factor[a+b*x+c*x^2+d*x^3]},
  FreeFactors[u,x]^p*Int[(e+f*x)^m*DistributeDegree[NonfreeFactors[u,x],p],x] /;
 ProductQ[NonfreeFactors[u,x]]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  1/(3^(3*p)*d^(2*p))*
    Int[(e+f*x)^m*(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NegativeIntegerQ[p] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c] *)


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  (a+b*x+c*x^2+d*x^3)^p/(b+c*x)^(3*p)*Int[(e+f*x)^m*(b+c*x)^(3*p),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[b^3-3*a*b*c,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p)*
    Int[(e+f*x)^m*(b-r+c*x)^p*(b+(1-I*Sqrt[3])*r/2+c*x)^p*(b+(1+I*Sqrt[3])*r/2+c*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ZeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[c^3-3*b*c*d,3]},
  (a+b*x+c*x^2+d*x^3)^p/((b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p)*
    Int[(e+f*x)^m*(b+(c-r)*x)^p*(b+(c+(1-I*Sqrt[3])*r/2)*x)^p*(b+(c+(1+I*Sqrt[3])*r/2)*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && ZeroQ[b^2-3*a*c]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{u=NonfreeFactors[Factor[a+b*x+c*x^2+d*x^3],x]},
  (a+b*x+c*x^2+d*x^3)^p/DistributeDegree[u,p]*Int[(e+f*x)^m*DistributeDegree[u,p],x] /;
 ProductQ[u]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


(* Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  1/(3^(3*p)*d^(2*p))*Subst[Int[(2*c^3-9*b*c*d+27*a*d^2-9*d*(c^2-3*b*d)*x+27*d^3*x^3)^p,x],x,x+c/(3*d)] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] *)


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
  With[{r=Rt[-2*c^3+9*b*c*d-27*a*d^2+3*Sqrt[3]*d*Sqrt[-b^2*c^2+4*a*c^3+4*b^3*d-18*a*b*c*d+27*a^2*d^2],3]},
  (a+b*x+c*x^2+d*x^3)^p/
    ((c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p)*
    Int[(e+f*x)^m*(c-(2*c^2-6*b*d+2^(1/3)*r^2)/(2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1+I*Sqrt[3])*c^2-6*(1+I*Sqrt[3])*b*d-I*2^(1/3)*(I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p*
      (c+(2*(1-I*Sqrt[3])*c^2-6*(1-I*Sqrt[3])*b*d+I*2^(1/3)*(-I+Sqrt[3])*r^2)/(2*2^(2/3)*r)+3*d*x)^p,x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && NonzeroQ[c^2-3*b*d] && NonzeroQ[b^2-3*a*c]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && LinearQ[u,x] && PolyQ[v,x,3] && Not[LinearMatchQ[u,x] && CubicMatchQ[v,x]]





(* ::Subsection::Closed:: *)
(*5.2 u (a+b x+c x^2+d x^3+e x^4)^p*)


Int[(f_+g_.*x_^2)/((d_+e_.*x_+d_.*x_^2)*Sqrt[a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4]),x_Symbol] :=
  a*f/(d*Rt[a^2*(2*a-c),2])*ArcTan[(a*b+(4*a^2+b^2-2*a*c)*x+a*b*x^2)/(2*Rt[a^2*(2*a-c),2]*Sqrt[a+b*x+c*x^2+b*x^3+a*x^4])] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[b*d-a*e] && ZeroQ[f+g] && PosQ[a^2*(2*a-c)]


Int[(f_+g_.*x_^2)/((d_+e_.*x_+d_.*x_^2)*Sqrt[a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4]),x_Symbol] :=
  -a*f/(d*Rt[-a^2*(2*a-c),2])*ArcTanh[(a*b+(4*a^2+b^2-2*a*c)*x+a*b*x^2)/(2*Rt[-a^2*(2*a-c),2]*Sqrt[a+b*x+c*x^2+b*x^3+a*x^4])] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[b*d-a*e] && ZeroQ[f+g] && NegQ[a^2*(2*a-c)]


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  Subst[Int[SimplifyIntegrand[(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[d^3-4*c*d*e+8*b*e^2] && p=!=2 && p=!=3


Int[v_^p_,x_Symbol] :=
  With[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  Subst[Int[SimplifyIntegrand[(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
 ZeroQ[d^3-4*c*d*e+8*b*e^2] && NonzeroQ[d]] /;
FreeQ[p,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && p=!=2 && p=!=3


Int[u_*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  Subst[Int[SimplifyIntegrand[ReplaceAll[u,x->-d/(4*e)+x]*(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
FreeQ[{a,b,c,d,e,p},x] && PolynomialQ[u,x] && ZeroQ[d^3-4*c*d*e+8*b*e^2] && Not[PositiveIntegerQ[p]]


Int[u_*v_^p_,x_Symbol] :=
  With[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  Subst[Int[SimplifyIntegrand[ReplaceAll[u,x->-d/(4*e)+x]*(a+d^4/(256*e^3)-b*d/(8*e)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x],x,d/(4*e)+x] /;
 ZeroQ[d^3-4*c*d*e+8*b*e^2] && NonzeroQ[d]] /;
FreeQ[p,x] && PolynomialQ[u,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && Not[PositiveIntegerQ[p]]


Int[(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
  -16*a^2*Subst[
    Int[1/(b-4*a*x)^2*(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p,x],x,b/(4*a)+1/x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^3-4*a*b*c+8*a^2*d] && IntegerQ[2*p]


Int[v_^p_,x_Symbol] :=
  With[{a=Coefficient[v,x,0],b=Coefficient[v,x,1],c=Coefficient[v,x,2],d=Coefficient[v,x,3],e=Coefficient[v,x,4]},
  -16*a^2*Subst[
    Int[1/(b-4*a*x)^2*(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p,x],x,b/(4*a)+1/x] /;
 NonzeroQ[a] && NonzeroQ[b] && ZeroQ[b^3-4*a*b*c+8*a^2*d]] /;
FreeQ[p,x] && PolynomialQ[v,x] && Exponent[v,x]==4 && IntegerQ[2*p]


Int[(A_.+B_.*x_+C_.*x_^2+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[(b*A-2*a*B+2*a*D+A*q+(2*a*A-2*a*C+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[(b*A-2*a*B+2*a*D-A*q+(2*a*A-2*a*C+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,C,D},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


Int[(A_.+B_.*x_+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[(b*A-2*a*B+2*a*D+A*q+(2*a*A+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[(b*A-2*a*B+2*a*D-A*q+(2*a*A+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,D},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


Int[x_^m_.*(A_.+B_.*x_+C_.*x_^2+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[x^m*(b*A-2*a*B+2*a*D+A*q+(2*a*A-2*a*C+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[x^m*(b*A-2*a*B+2*a*D-A*q+(2*a*A-2*a*C+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,C,D,m},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


Int[x_^m_.*(A_.+B_.*x_+D_.*x_^3)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
  With[{q=Sqrt[8*a^2+b^2-4*a*c]},
  1/q*Int[x^m*(b*A-2*a*B+2*a*D+A*q+(2*a*A+b*D+D*q)*x)/(2*a+(b+q)*x+2*a*x^2),x] -
  1/q*Int[x^m*(b*A-2*a*B+2*a*D-A*q+(2*a*A+b*D-D*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]] /;
FreeQ[{a,b,c,A,B,D,m},x] && ZeroQ[d-b] && ZeroQ[e-a] && SumQ[Factor[a+b*x+c*x^2+b*x^3+a*x^4]]


(* ::Subsection::Closed:: *)
(*5.3 Miscellaneous algebraic functions*)


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  c/(e*(b*c-a*d))*Int[(u*Sqrt[a+b*x])/x,x] - a/(f*(b*c-a*d))*Int[(u*Sqrt[c+d*x])/x,x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[a*e^2-c*f^2]


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  -d/(e*(b*c-a*d))*Int[u*Sqrt[a+b*x],x] + b/(f*(b*c-a*d))*Int[u*Sqrt[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && ZeroQ[b*e^2-d*f^2]


Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  e*Int[(u*Sqrt[a+b*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x] - 
  f*Int[(u*Sqrt[c+d*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a*e^2-c*f^2] && NonzeroQ[b*e^2-d*f^2]


Int[u_./(d_.*x_^n_.+c_.*Sqrt[a_.+b_.*x_^p_.]),x_Symbol] :=
  -b/(a*d)*Int[u*x^n,x] + 1/(a*c)*Int[u*Sqrt[a+b*x^(2*n)],x] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[p-2*n] && ZeroQ[b*c^2-d^2]


Int[x_^m_./(d_.*x_^n_.+c_.*Sqrt[a_.+b_.*x_^p_.]),x_Symbol] :=
  -d*Int[x^(m+n)/(a*c^2+(b*c^2-d^2)*x^(2*n)),x] + 
  c*Int[(x^m*Sqrt[a+b*x^(2*n)])/(a*c^2+(b*c^2-d^2)*x^(2*n)),x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[p-2*n] && NonzeroQ[b*c^2-d^2]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  r/(3*a)*Int[1/((r+s*x)*Sqrt[d+e*x+f*x^2]),x] +
  r/(3*a)*Int[(2*r-s*x)/((r^2-r*s*x+s^2*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,d,e,f},x] && PosQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  r/(3*a)*Int[1/((r+s*x)*Sqrt[d+f*x^2]),x] +
  r/(3*a)*Int[(2*r-s*x)/((r^2-r*s*x+s^2*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,d,f},x] && PosQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r/(3*a)*Int[1/((r-s*x)*Sqrt[d+e*x+f*x^2]),x] +
  r/(3*a)*Int[(2*r+s*x)/((r^2+r*s*x+s^2*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,d,e,f},x] && NegQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r/(3*a)*Int[1/((r-s*x)*Sqrt[d+f*x^2]),x] +
  r/(3*a)*Int[(2*r+s*x)/((r^2+r*s*x+s^2*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,d,f},x] && NegQ[a/b]


Int[1/((d_+e_.*x_)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*Sqrt[a+b*x^2+c*x^4]),x] - e*Int[x/((d^2-e^2*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
FreeQ[{a,b,c,d,e},x]


Int[1/((d_+e_.*x_)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*Sqrt[a+c*x^4]),x] - e*Int[x/((d^2-e^2*x^2)*Sqrt[a+c*x^4]),x] /;
FreeQ[{a,c,d,e},x]


Int[1/((d_+e_.*x_)^2*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  -e^3*Sqrt[a+b*x^2+c*x^4]/((c*d^4+b*d^2*e^2+a*e^4)*(d+e*x)) - 
  c/(c*d^4+b*d^2*e^2+a*e^4)*Int[(d^2-e^2*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[c*d^4+b*d^2*e^2+a*e^4] && ZeroQ[2*c*d^3+b*d*e^2]


Int[1/((d_+e_.*x_)^2*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  -e^3*Sqrt[a+b*x^2+c*x^4]/((c*d^4+b*d^2*e^2+a*e^4)*(d+e*x)) - 
  c/(c*d^4+b*d^2*e^2+a*e^4)*Int[(d^2-e^2*x^2)/Sqrt[a+b*x^2+c*x^4],x] + 
  (2*c*d^3+b*d*e^2)/(c*d^4+b*d^2*e^2+a*e^4)*Int[1/((d+e*x)*Sqrt[a+b*x^2+c*x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[c*d^4+b*d^2*e^2+a*e^4] && NonzeroQ[2*c*d^3+b*d*e^2]


Int[1/((d_+e_.*x_)^2*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  -e^3*Sqrt[a+c*x^4]/((c*d^4+a*e^4)*(d+e*x)) - 
  c/(c*d^4+a*e^4)*Int[(d^2-e^2*x^2)/Sqrt[a+c*x^4],x] + 
  2*c*d^3/(c*d^4+a*e^4)*Int[1/((d+e*x)*Sqrt[a+c*x^4]),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^4+a*e^4]


Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d-(b*d-2*a*e)*x^2),x],x,x/Sqrt[a+b*x^2+c*x^4]] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[B*d+A*e] && ZeroQ[c*d^2-a*e^2]


Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d+2*a*e*x^2),x],x,x/Sqrt[a+c*x^4]] /;
FreeQ[{a,c,d,e,A,B},x] && ZeroQ[B*d+A*e] && ZeroQ[c*d^2-a*e^2]


Int[(A_+B_.*x_^4)/((d_+e_.*x_^2+f_.*x_^4)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d-(b*d-a*e)*x^2),x],x,x/Sqrt[a+b*x^2+c*x^4]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && ZeroQ[c*d-a*f] && ZeroQ[a*B+A*c]


Int[(A_+B_.*x_^4)/((d_+e_.*x_^2+f_.*x_^4)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d+a*e*x^2),x],x,x/Sqrt[a+c*x^4]] /;
FreeQ[{a,c,d,e,f,A,B},x] && ZeroQ[c*d-a*f] && ZeroQ[a*B+A*c]


Int[(A_+B_.*x_^4)/((d_+f_.*x_^4)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  A*Subst[Int[1/(d-b*d*x^2),x],x,x/Sqrt[a+b*x^2+c*x^4]] /;
FreeQ[{a,b,c,d,f,A,B},x] && ZeroQ[c*d-a*f] && ZeroQ[a*B+A*c]


Int[1/((a_+b_.*x_)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  a*Int[1/((a^2-b^2*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] - b*Int[x/((a^2-b^2*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x]


Int[(g_.+h_.*x_)*Sqrt[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  2*(f*(5*b*c*g^2-2*b^2*g*h-3*a*c*g*h+2*a*b*h^2)+c*f*(10*c*g^2-b*g*h+a*h^2)*x+9*c^2*f*g*h*x^2+3*c^2*f*h^2*x^3-
    (e*g-d*h)*(5*c*g-2*b*h+c*h*x)*Sqrt[a+b*x+c*x^2])/
  (15*c^2*f*(g+h*x))*Sqrt[d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && ZeroQ[(e*g-d*h)^2-f^2*(c*g^2-b*g*h+a*h^2)] && ZeroQ[2*e^2*g-2*d*e*h-f^2*(2*c*g-b*h)]


Int[(g_.+h_.*x_)^m_.*(u_+f_.*(j_.+k_.*Sqrt[v_]))^n_.,x_Symbol] :=
  Int[(g+h*x)^m*(ExpandToSum[u+f*j,x]+f*k*Sqrt[ExpandToSum[v,x]])^n,x] /;
FreeQ[{f,g,h,j,k,m,n},x] && LinearQ[u,x] && QuadraticQ[v,x] && 
  Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x] && (ZeroQ[j] || ZeroQ[f-1])] && 
  ZeroQ[(Coefficient[u,x,1]*g-h*(Coefficient[u,x,0]+f*j))^2-f^2*k^2*(Coefficient[v,x,2]*g^2-Coefficient[v,x,1]*g*h+Coefficient[v,x,0]*h^2)]


(* Int[1/(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  Int[(d+e*x)/(d^2-a*f^2+(2*d*e-b*f^2)*x),x] - 
  f*Int[Sqrt[a+b*x+c*x^2]/(d^2-a*f^2+(2*d*e-b*f^2)*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[e^2-c*f^2] *)


(* Int[1/(d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]),x_Symbol] :=
  Int[(d+e*x)/(d^2-a*f^2+2*d*e*x),x] - 
  f*Int[Sqrt[a+c*x^2]/(d^2-a*f^2+2*d*e*x),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[e^2-c*f^2] *)


Int[(g_.+h_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_)^p_.,x_Symbol] :=
  2*Subst[Int[(g+h*x^n)^p*(d^2*e-(b*d-a*e)*f^2-(2*d*e-b*f^2)*x+e*x^2)/(-2*d*e+b*f^2+2*e*x)^2,x],x,d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h,n},x] && ZeroQ[e^2-c*f^2] && IntegerQ[p]


Int[(g_.+h_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_)^p_.,x_Symbol] :=
  1/(2*e)*Subst[Int[(g+h*x^n)^p*(d^2+a*f^2-2*d*x+x^2)/(d-x)^2,x],x,d+e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e,f,g,h,n},x] && ZeroQ[e^2-c*f^2] && IntegerQ[p]


Int[(g_.+h_.*(u_+f_. Sqrt[v_])^n_)^p_.,x_Symbol] :=
  Int[(g+h*(ExpandToSum[u,x]+f*Sqrt[ExpandToSum[v,x]])^n)^p,x] /;
FreeQ[{f,g,h,n},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]] && 
  ZeroQ[Coefficient[u,x,1]^2-Coefficient[v,x,2]*f^2] && IntegerQ[p]


Int[(g_.+h_.*x_)^m_.*(e_.*x_+f_.*Sqrt[a_.+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(m+1)*e^(m+1))*Subst[Int[x^(n-m-2)*(a*f^2+x^2)*(-a*f^2*h+2*e*g*x+h*x^2)^m,x],x,e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,e,f,g,h,n},x] && ZeroQ[e^2-c*f^2] && IntegerQ[m]


Int[x_^p_.*(g_+i_.*x_^2)^m_.*(e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(2*m+p+1)*e^(p+1)*f^(2*m))*(i/c)^m*Subst[Int[x^(n-2*m-p-2)*(-a*f^2+x^2)^p*(a*f^2+x^2)^(2*m+1),x],x,e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,e,f,g,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && IntegersQ[p,2*m] && (IntegerQ[m] || PositiveQ[i/c])


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  2/f^(2*m)*(i/c)^m*
    Subst[Int[x^n*(d^2*e-(b*d-a*e)*f^2-(2*d*e-b*f^2)*x+e*x^2)^(2*m+1)/(-2*d*e+b*f^2+2*e*x)^(2*(m+1)),x],x,d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && ZeroQ[c*h-b*i] && IntegerQ[2*m] && (IntegerQ[m] || PositiveQ[i/c])


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  1/(2^(2*m+1)*e*f^(2*m))*(i/c)^m*
    Subst[Int[x^n*(d^2+a*f^2-2*d*x+x^2)^(2*m+1)/(-d+x)^(2*(m+1)),x],x,d+e*x+f*Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && IntegerQ[2*m] && (IntegerQ[m] || PositiveQ[i/c])


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m-1/2)*Sqrt[g+h*x+i*x^2]/Sqrt[a+b*x+c*x^2]*Int[(a+b*x+c*x^2)^m*(d+e*x+f*Sqrt[a+b*x+c*x^2])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && ZeroQ[c*h-b*i] && PositiveIntegerQ[m+1/2] && Not[PositiveQ[i/c]]


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m-1/2)*Sqrt[g+i*x^2]/Sqrt[a+c*x^2]*Int[(a+c*x^2)^m*(d+e*x+f*Sqrt[a+c*x^2])^n,x] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && PositiveIntegerQ[m+1/2] && Not[PositiveQ[i/c]]


Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m+1/2)*Sqrt[a+b*x+c*x^2]/Sqrt[g+h*x+i*x^2]*Int[(a+b*x+c*x^2)^m*(d+e*x+f*Sqrt[a+b*x+c*x^2])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && ZeroQ[c*h-b*i] && NegativeIntegerQ[m-1/2] && Not[PositiveQ[i/c]]


Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
  (i/c)^(m+1/2)*Sqrt[a+c*x^2]/Sqrt[g+i*x^2]*Int[(a+c*x^2)^m*(d+e*x+f*Sqrt[a+c*x^2])^n,x] /;
FreeQ[{a,c,d,e,f,g,i,n},x] && ZeroQ[e^2-c*f^2] && ZeroQ[c*g-a*i] && NegativeIntegerQ[m-1/2] && Not[PositiveQ[i/c]]


Int[w_^m_.*(u_+f_.*(j_.+k_.*Sqrt[v_]))^n_.,x_Symbol] :=
  Int[ExpandToSum[w,x]^m*(ExpandToSum[u+f*j,x]+f*k*Sqrt[ExpandToSum[v,x]])^n,x] /;
FreeQ[{f,j,k,m,n},x] && LinearQ[u,x] && QuadraticQ[{v,w},x] && 
  Not[LinearMatchQ[u,x] && QuadraticMatchQ[{v,w},x] && (ZeroQ[j] || ZeroQ[f-1])] && 
  ZeroQ[Coefficient[u,x,1]^2-Coefficient[v,x,2]*f^2*k^2]


Int[1/((a_+b_.*x_^n_.)*Sqrt[c_.*x_^2+d_.*(a_+b_.*x_^n_.)^p_.]),x_Symbol] :=
  1/a*Subst[Int[1/(1-c*x^2),x],x,x/Sqrt[c*x^2+d*(a+b*x^n)^(2/n)]] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[p-2/n]


Int[Sqrt[a_+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
  2*b^2*d*x^3/(3*(a+b*Sqrt[c+d*x^2])^(3/2)) + 2*a*x/Sqrt[a+b*Sqrt[c+d*x^2]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2*c]


Int[Sqrt[a_.*x_^2+b_.*x_*Sqrt[c_+d_.*x_^2]]/(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[2]*b/a*Subst[Int[1/Sqrt[1+x^2/a],x],x,a*x+b*Sqrt[c+d*x^2]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2*d] && ZeroQ[b^2*c+a]


Int[Sqrt[e_.*x_*(a_.*x_+b_.*Sqrt[c_+d_.*x_^2])]/(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Int[Sqrt[a*e*x^2+b*e*x*Sqrt[c+d*x^2]]/(x*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2*d] && ZeroQ[b^2*c*e+a]


Int[Sqrt[c_.*x_^2+d_.*Sqrt[a_+b_.*x_^4]]/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  d*Subst[Int[1/(1-2*c*x^2),x],x,x/Sqrt[c*x^2+d*Sqrt[a+b*x^4]]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[c^2-b*d^2]


Int[(c_.+d_.*x_)^m_.*Sqrt[b_.*x_^2+Sqrt[a_+e_.*x_^4]]/Sqrt[a_+e_.*x_^4],x_Symbol] :=
  (1-I)/2*Int[(c+d*x)^m/Sqrt[Sqrt[a]-I*b*x^2],x] +
  (1+I)/2*Int[(c+d*x)^m/Sqrt[Sqrt[a]+I*b*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[e-b^2] && PositiveQ[a]


Int[(A_+B_.*x_^n_)/(a_+b_.*x_^2+c_.*x_^n_+d_.*x_^n2_), x_Symbol] :=
  A^2*(n-1)*Subst[Int[1/(a+A^2*b*(n-1)^2*x^2),x],x,x/(A*(n-1)-B*x^n)] /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[n2-2*n] && NonzeroQ[n-2] && ZeroQ[a*B^2-A^2*d*(n-1)^2] && ZeroQ[B*c+2*A*d*(n-1)]


Int[x_^m_.*(A_+B_.*x_^n_.)/(a_+b_.*x_^k_.+c_.*x_^n_.+d_.*x_^n2_), x_Symbol] :=
  A^2*(m-n+1)/(m+1)*Subst[Int[1/(a+A^2*b*(m-n+1)^2*x^2),x],x,x^(m+1)/(A*(m-n+1)+B*(m+1)*x^n)] /;
FreeQ[{a,b,c,d,A,B,m,n},x] && ZeroQ[n2-2*n] && ZeroQ[k-2*(m+1)] && ZeroQ[a*B^2*(m+1)^2-A^2*d*(m-n+1)^2] && ZeroQ[B*c*(m+1)-2*A*d*(m-n+1)]


Int[(d_+e_.*x_^n_+f_.*x_^n2_+g_*x_^n3_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(b^2*c*d-2*a*c*(c*d-a*f)-a*b*(c*e+a*g)+(b*c*(c*d+a*f)-a*b^2*g-2*a*c*(c*e-a*g))*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/
    (a*c*n*(p+1)*(b^2-4*a*c)) - 
  1/(a*c*n*(p+1)*(b^2-4*a*c))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*
    Simp[a*b*(c*e+a*g)-b^2*c*d*(n+n*p+1)-2*a*c*(a*f-c*d*(2*n*(p+1)+1))+
      (a*b^2*g*(n*(p+2)+1)-b*c*(c*d+a*f)*(n*(2*p+3)+1)-2*a*c*(a*g*(n+1)-c*e*(n*(2*p+3)+1)))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && ZeroQ[n2-2*n] && ZeroQ[n3-3*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(d_+e_.*x_^n_+f_.*x_^n2_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(b^2*d-2*a*(c*d-a*f)-a*b*e+(b*(c*d+a*f)-2*a*c*e)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) - 
  1/(a*n*(p+1)*(b^2-4*a*c))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*
    Simp[a*b*e-b^2*d*(n+n*p+1)-2*a*(a*f-c*d*(2*n*(p+1)+1))-
      (b*(c*d+a*f)*(n*(2*p+3)+1)-2*a*c*e*(n*(2*p+3)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(d_+e_.*x_^n_+g_*x_^n3_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(b^2*c*d-2*a*c^2*d-a*b*(c*e+a*g)+(b*c^2*d-a*b^2*g-2*a*c*(c*e-a*g))*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/
    (a*c*n*(p+1)*(b^2-4*a*c)) - 
  1/(a*c*n*(p+1)*(b^2-4*a*c))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*
    Simp[a*b*(c*e+a*g)-b^2*c*d*(n+n*p+1)+2*a*c^2*d*(2*n*(p+1)+1)+
      (a*b^2*g*(n*(p+2)+1)-b*c^2*d*(n*(2*p+3)+1)-2*a*c*(a*g*(n+1)-c*e*(n*(2*p+3)+1)))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,g,n},x] && ZeroQ[n2-2*n] && ZeroQ[n3-3*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(d_+f_.*x_^n2_+g_*x_^n3_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(b^2*c*d-2*a*c*(c*d-a*f)-a^2*b*g+(b*c*(c*d+a*f)-a*b^2*g+2*a^2*c*g)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/
    (a*c*n*(p+1)*(b^2-4*a*c)) - 
  1/(a*c*n*(p+1)*(b^2-4*a*c))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*
    Simp[a^2*b*g-b^2*c*d*(n+n*p+1)-2*a*c*(a*f-c*d*(2*n*(p+1)+1))+
      (a*b^2*g*(n*(p+2)+1)-b*c*(c*d+a*f)*(n*(2*p+3)+1)-2*a^2*c*g*(n+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,f,g,n},x] && ZeroQ[n2-2*n] && ZeroQ[n3-3*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(d_+f_.*x_^n2_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(b^2*d-2*a*(c*d-a*f)+b*(c*d+a*f)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*
    Simp[b^2*d*(n+n*p+1)+2*a*(a*f-c*d*(2*n*(p+1)+1))+b*(c*d+a*f)*(n*(2*p+3)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,f,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(d_+g_*x_^n3_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(b^2*c*d-2*a*c^2*d-a^2*b*g+(b*c^2*d-a*b^2*g+2*a^2*c*g)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/
    (a*c*n*(p+1)*(b^2-4*a*c)) - 
  1/(a*c*n*(p+1)*(b^2-4*a*c))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*
    Simp[a^2*b*g-b^2*c*d*(n+n*p+1)+2*a*c^2*d*(2*n*(p+1)+1)+
      (a*b^2*g*(n*(p+2)+1)-b*c^2*d*(n*(2*p+3)+1)-2*a*c*(a*g*(n+1)))*x^n,x],x] /;
FreeQ[{a,b,c,d,g,n},x] && ZeroQ[n2-2*n] && ZeroQ[n3-3*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(d_+e_.*x_^n_+f_.*x_^n2_+g_*x_^n3_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(-2*a*c*(c*d-a*f)+(-2*a*c*(c*e-a*g))*x^n)*(a+c*x^(2*n))^(p+1)/
    (a*c*n*(p+1)*(-4*a*c)) - 
  1/(a*c*n*(p+1)*(-4*a*c))*Int[(a+c*x^(2*n))^(p+1)*
    Simp[-2*a*c*(a*f-c*d*(2*n*(p+1)+1))+
      (-2*a*c*(a*g*(n+1)-c*e*(n*(2*p+3)+1)))*x^n,x],x] /;
FreeQ[{a,c,d,e,f,g,n},x] && ZeroQ[n2-2*n] && ZeroQ[n3-3*n] && NegativeIntegerQ[p+1]


Int[(d_+e_.*x_^n_+f_.*x_^n2_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(-2*a*(c*d-a*f)+(-2*a*c*e)*x^n)*(a+c*x^(2*n))^(p+1)/(a*n*(p+1)*(-4*a*c)) - 
  1/(a*n*(p+1)*(-4*a*c))*Int[(a+c*x^(2*n))^(p+1)*
    Simp[-2*a*(a*f-c*d*(2*n*(p+1)+1))-
      (-2*a*c*e*(n*(2*p+3)+1))*x^n,x],x] /;
FreeQ[{a,c,d,e,f,n},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[p+1]


Int[(d_+e_.*x_^n_+g_*x_^n3_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(-2*a*c^2*d+(-2*a*c*(c*e-a*g))*x^n)*(a+c*x^(2*n))^(p+1)/
    (a*c*n*(p+1)*(-4*a*c)) - 
  1/(a*c*n*(p+1)*(-4*a*c))*Int[(a+c*x^(2*n))^(p+1)*
    Simp[2*a*c^2*d*(2*n*(p+1)+1)+
      (-2*a*c*(a*g*(n+1)-c*e*(n*(2*p+3)+1)))*x^n,x],x] /;
FreeQ[{a,c,d,e,g,n},x] && ZeroQ[n2-2*n] && ZeroQ[n3-3*n] && NegativeIntegerQ[p+1]


If[ShowSteps,

Int[u_*v_^p_,x_Symbol] :=
  With[{m=Exponent[u,x],n=Exponent[v,x]},
  Module[{c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p)),w},
  w=Apart[u-c*x^(m-n)*((m-n+1)*v+(p+1)*x*D[v,x]),x];
  If[ZeroQ[w],
    ShowStep["
If p>1, 1<n<=m+1, and m+1-n*p<0, let c=pm/(qn*(m+1-n*p)), then if (Pm[x]-c*x^(m-n)*((m-n+1)*Qn[x]+(1-p)*x*D[Qn[x],x]))==0,",
	  "Int[Pm[x]/Qn[x]^p,x]", "c*x^(m-n+1)/Qn[x]^(p-1)",
      Hold[c*x^(m-n+1)*v^(p+1)]],
  ShowStep["If p>1, 1<n<=m+1, and m+1-n*p<0, let c=pm/(qn*(m+1-n*p)), then",
	"Int[Pm[x]/Qn[x]^p,x]",
	"c*x^(m-n+1)/Qn[x]^(p-1)+Int[(Pm[x]-c*x^(m-n)*((m-n+1)*Qn[x]+(1-p)*x*D[Qn[x],x]))/Qn[x]^p,x]",
	Hold[c*x^(m-n+1)*v^(p+1) + Int[w*v^p,x]]]]] /;
 1<n<=m+1 && m+n*p<-1 && FalseQ[DerivativeDivides[v,u,x]]] /;
SimplifyFlag && RationalQ[p] && p<-1 && PolynomialQ[u,x] && PolynomialQ[v,x] && SumQ[v] && 
Not[MonomialQ[u,x] && BinomialQ[v,x]] && 
Not[ZeroQ[Coefficient[u,x,0]] && ZeroQ[Coefficient[v,x,0]]],

Int[u_*v_^p_,x_Symbol] :=
  With[{m=Exponent[u,x],n=Exponent[v,x]},
  Module[{c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p)),w},
  c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p));
  w=Apart[u-c*x^(m-n)*((m-n+1)*v+(p+1)*x*D[v,x]),x];
  If[ZeroQ[w],
    c*x^(m-n+1)*v^(p+1),
  c*x^(m-n+1)*v^(p+1) + Int[w*v^p,x]]] /;
 1<n<=m+1 && m+n*p<-1 && FalseQ[DerivativeDivides[v,u,x]]] /;
RationalQ[p] && p<-1 && PolynomialQ[u,x] && PolynomialQ[v,x] && SumQ[v] && 
Not[MonomialQ[u,x] && BinomialQ[v,x]] && 
Not[ZeroQ[Coefficient[u,x,0]] && ZeroQ[Coefficient[v,x,0]]]]



