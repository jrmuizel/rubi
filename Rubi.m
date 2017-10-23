(* ::Package:: *)

(* ::Title:: *)
(*Rubi (Rule-Based Integrator) Package*)


BeginPackage["Rubi`"];


Int::usage = 
"Int[expn,var] returns the antiderivative (indefinite integral) of <expn> with respect to <var>.
Int[list,var] returns a list of the antiderivatives of the elements of <list> with respect to <var>.";


IntShowSteps::usage = "IntShowSteps[expn,var] shows all the rules and intermediate steps required to integrate <expn> with respect to <var>, and returns Null.";


Dist::usage = "Dist[expn1,expn2,var] distributes <expn1> over <expn2>.";
Subst::usage = "Subst[expn1,var,expn2] substitutes <expn2> for <var> in <expn1>.";


ShowSteps::usage = "If ShowSteps is True and the ShowSteps package has been loaded, integration steps are displayed.";
$StepCounter::usage = "If the ShowSteps package has been loaded and $StepCounter is an integer, it is incremented each time an integration rule is applied.";


$RuleColor::usage = "$RuleColor is the color used to display rules when showing integration steps. The default rule color is red."
$ConditionColor::usage = "$ConditionColor is the color used to display application conditions when showing integration steps. The default condition color is blue."


sin::usage = "Inert sine function";
cos::usage = "Inert cosine function";
tan::usage = "Inert tangent function";
cot::usage = "Inert cotangent function";
sec::usage = "Inert secant function";
csc::usage = "Inert cosecant function";


Begin["`Private`"];


LoadRules[filename_String] :=
  Module[{object},
  object=PrintTemporary["Loading "<>filename<>".m..."];
  Get[FileNameJoin[{NotebookDirectory[],filename<>".m"}]];
  NotebookDelete[object];
  Null]


Unprotect[Int];  Clear[Int];


SetAttributes [Int, {Listable}];


ShowSteps = Global`$LoadShowSteps===True;


Integral[u_,x_] := Defer[Int][u,x]


LoadRules["ShowStep routines"];
LoadRules["Integration utility functions"];
LoadRules["9.1 Integrand simplification rules"];


LoadRules["1.1.1 Linear binomial products"];
LoadRules["1.1.3 General binomial products"];
LoadRules["1.2.1 Quadratic trinomial products"];
LoadRules["1.1.2 Quadratic binomial products"];
LoadRules["1.2.2 Quartic trinomial products"];
LoadRules["1.2.3 General trinomial products"];
LoadRules["1.2.4 Improper trinomial products"];
LoadRules["1.1.4 Improper binomial products"];
LoadRules["1.3 Miscellaneous algebraic functions"];
LoadRules["9.3 Piecewise linear functions"];


LoadRules["2 Exponentials"];
LoadRules["3 Logarithms"];
LoadRules["4.1 Sine"];
LoadRules["4.2 Tangent"];
LoadRules["4.3 Secant"];
LoadRules["4.4 Miscellaneous trig functions"];
LoadRules["5 Inverse trig functions"];
LoadRules["6 Hyperbolic functions"];
LoadRules["7 Inverse hyperbolic functions"];
LoadRules["8 Special functions"];
LoadRules["9.2 Derivative integration rules"];
LoadRules["9.4 Miscellaneous integration rules"];


FixIntRules[];


If[Global`$LoadShowSteps===True, StepFunction[Int]];


Protect[Int];


End [];
EndPackage [];
