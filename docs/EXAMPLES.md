# Rubi Integration Examples

This guide provides comprehensive examples of symbolic integration using Rubi, organized by function type and complexity level. Each example includes the input expression, the result, and often shows the step-by-step process.

## Table of Contents

- [Getting Started](#getting-started)
- [Polynomial and Rational Functions](#polynomial-and-rational-functions)
- [Exponential Functions](#exponential-functions)
- [Logarithmic Functions](#logarithmic-functions)
- [Trigonometric Functions](#trigonometric-functions)
- [Inverse Trigonometric Functions](#inverse-trigonometric-functions)
- [Hyperbolic Functions](#hyperbolic-functions)
- [Special Functions](#special-functions)
- [Mixed Function Types](#mixed-function-types)
- [Advanced Techniques](#advanced-techniques)
- [Step-by-Step Examples](#step-by-step-examples)
- [Performance Comparison](#performance-comparison)

## Getting Started

### Loading Rubi

```mathematica
(* Basic loading *)
Get["Rubi.m"]

(* Loading with step-by-step capability *)
$LoadShowSteps = True;
Get["Rubi.m"]

(* Or load compiled version for faster startup *)
Get["Rubi.mx"]
```

### Basic Integration Syntax

```mathematica
(* Basic indefinite integral *)
Int[expression, x]

(* Multiple expressions *)
Int[{expr1, expr2, expr3}, x]

(* Definite integral (limits of antiderivative) *)
Int[expression, {x, a, b}]

(* With step display *)
Int[expression, x, Steps]
```

## Polynomial and Rational Functions

### Basic Polynomials

```mathematica
(* Power functions *)
Int[x^3, x]
(* Result: x^4/4 *)

Int[x^(-2), x]
(* Result: -1/x *)

Int[1/x, x]
(* Result: Log[x] *)

(* Polynomial combinations *)
Int[3*x^2 + 2*x + 1, x]
(* Result: x^3 + x^2 + x *)

Int[(x + 1)^5, x]
(* Result: (1 + x)^6/6 *)
```

### Rational Functions

```mathematica
(* Simple rational functions *)
Int[1/(x + 1), x]
(* Result: Log[1 + x] *)

Int[1/(x^2 + 1), x]
(* Result: ArcTan[x] *)

Int[x/(x^2 + 1), x]
(* Result: Log[1 + x^2]/2 *)

(* Partial fraction decomposition *)
Int[1/((x - 1)*(x + 2)), x]
(* Result: Log[1 - x]/3 + Log[2 + x]/3 *)

Int[(2*x + 3)/((x - 1)*(x + 2)), x]
(* Result: (5*Log[1 + x/2])/3 + (7*Log[1 - x])/3 *)
```

### Binomial and Trinomial Products

```mathematica
(* Linear binomials *)
Int[x*(a + b*x)^n, x]
(* General result for various values of n *)

Int[x^2*(1 + x)^3, x]
(* Result: x^3/3 + x^4/2 + 3*x^5/5 + x^6/6 *)

(* Square roots *)
Int[Sqrt[1 + x], x]
(* Result: (2*(1 + x)^(3/2))/3 *)

Int[x*Sqrt[1 + x^2], x]
(* Result: (1 + x^2)^(3/2)/3 *)

(* Trinomials *)
Int[1/Sqrt[a + b*x + c*x^2], x]
(* Result varies based on discriminant *)
```

## Exponential Functions

### Basic Exponential Integrals

```mathematica
(* Simple exponentials *)
Int[E^x, x]
(* Result: E^x *)

Int[E^(a*x), x]
(* Result: E^(a*x)/a *)

Int[2^x, x]
(* Result: 2^x/Log[2] *)

(* Exponential products *)
Int[x*E^x, x]
(* Result: E^x*(-1 + x) *)

Int[x^2*E^x, x]
(* Result: E^x*(-2 + 2*x + x^2) *)

Int[x^n*E^x, x]  (* General case *)
(* Recursive integration by parts *)
```

### Exponential-Polynomial Combinations

```mathematica
(* Linear combinations *)
Int[(a + b*x)*E^(c*x), x]
(* Result: (E^(c*x)*(a*c + b*(-1 + c*x)))/c^2 *)

Int[x^3*E^(-x), x]
(* Result: -E^(-x)*(6 + 6*x + 3*x^2 + x^3) *)

(* Rational exponentials *)
Int[E^x/(1 + E^x), x]
(* Result: Log[1 + E^x] *)

Int[E^x/(1 + E^(2*x)), x]
(* Result: ArcTan[E^x] *)
```

### Exponential Functions with Other Bases

```mathematica
(* Different bases *)
Int[3^(2*x), x]
(* Result: 3^(2*x)/(2*Log[3]) *)

Int[x*a^(b*x), x]
(* Result: (a^(b*x)*(-1 + b*x*Log[a]))/(b^2*Log[a]^2) *)
```

## Logarithmic Functions

### Basic Logarithmic Integrals

```mathematica
(* Simple logarithms *)
Int[Log[x], x]
(* Result: -x + x*Log[x] *)

Int[Log[a*x], x]
(* Result: -x + x*Log[a*x] *)

Int[x*Log[x], x]
(* Result: x^2/4*(-1 + 2*Log[x]) *)

(* Logarithmic products *)
Int[x^n*Log[x], x]
(* Result: x^(1+n)/(1+n)^2*(-1 + (1+n)*Log[x]) *)
```

### Logarithms with Different Arguments

```mathematica
(* Linear arguments *)
Int[Log[a + b*x], x]
(* Result: ((a + b*x)*Log[a + b*x])/b - x *)

Int[x*Log[1 + x], x]
(* Result: x^2/4*(-1 + 2*Log[1 + x]) *)

(* Quadratic arguments *)
Int[Log[1 + x^2], x]
(* Result: -2*x + x*Log[1 + x^2] + 2*ArcTan[x] *)

Int[x*Log[1 + x^2], x]
(* Result: ((1 + x^2)*Log[1 + x^2])/2 - x^2/2 *)
```

### Multiple Logarithms

```mathematica
(* Products of logarithms *)
Int[Log[x]*Log[1 + x], x]
(* Complex expression involving polylogarithms *)

Int[Log[x]/x, x]
(* Result: Log[x]^2/2 *)

Int[Log[x]^2, x]
(* Result: x*(2 - 2*Log[x] + Log[x]^2) *)
```

## Trigonometric Functions

### Basic Trigonometric Integrals

```mathematica
(* Basic trig functions *)
Int[Sin[x], x]
(* Result: -Cos[x] *)

Int[Cos[x], x]
(* Result: Sin[x] *)

Int[Tan[x], x]
(* Result: -Log[Cos[x]] *)

Int[Sec[x], x]
(* Result: Log[Sec[x] + Tan[x]] *)

(* With linear arguments *)
Int[Sin[a + b*x], x]
(* Result: -Cos[a + b*x]/b *)

Int[Cos[a*x], x]
(* Result: Sin[a*x]/a *)
```

### Powers of Trigonometric Functions

```mathematica
(* Sine powers *)
Int[Sin[x]^2, x]
(* Result: x/2 - Sin[2*x]/4 *)

Int[Sin[x]^3, x]
(* Result: -Cos[x] + Cos[x]^3/3 *)

Int[Sin[x]^n, x]  (* General case for integer n *)

(* Cosine powers *)
Int[Cos[x]^2, x]
(* Result: x/2 + Sin[2*x]/4 *)

Int[Cos[x]^4, x]
(* Result: (3*x)/8 + (3*Sin[2*x])/16 + Sin[4*x]/32 *)

(* Tangent powers *)
Int[Tan[x]^2, x]
(* Result: -x + Tan[x] *)

Int[Tan[x]^3, x]
(* Result: -Log[Cos[x]] + Tan[x]^2/2 *)
```

### Products of Trigonometric Functions

```mathematica
(* Sine-cosine products *)
Int[Sin[x]*Cos[x], x]
(* Result: Sin[x]^2/2 *)

Int[Sin[a*x]*Cos[b*x], x]
(* Result depends on relationship between a and b *)

Int[Sin[x]^2*Cos[x]^2, x]
(* Result: x/8 - Sin[4*x]/32 *)

(* Mixed products *)
Int[Sin[x]*Tan[x], x]
(* Result: Log[Cos[x]] + Sin[x]^2/2 *)

Int[x*Sin[x], x]
(* Result: -x*Cos[x] + Sin[x] *)

Int[x^2*Cos[x], x]
(* Result: 2*Cos[x] + x^2*Sin[x] - 2*x*Cos[x] *)
```

## Inverse Trigonometric Functions

### Basic Inverse Trigonometric Integrals

```mathematica
(* Basic inverse trig functions *)
Int[ArcSin[x], x]
(* Result: x*ArcSin[x] + Sqrt[1 - x^2] *)

Int[ArcCos[x], x]
(* Result: x*ArcCos[x] - Sqrt[1 - x^2] *)

Int[ArcTan[x], x]
(* Result: x*ArcTan[x] - Log[1 + x^2]/2 *)

Int[ArcSec[x], x]
(* Result: x*ArcSec[x] - Log[x + Sqrt[-1 + x^2]] *)
```

### Inverse Trigonometric Functions with Arguments

```mathematica
(* Linear arguments *)
Int[ArcTan[a*x], x]
(* Result: (x*ArcTan[a*x])/a - Log[1 + a^2*x^2]/(2*a) *)

Int[ArcSin[a*x], x]
(* Result: (x*ArcSin[a*x])/a + Sqrt[1 - a^2*x^2]/a *)

(* Products with polynomials *)
Int[x*ArcTan[x], x]
(* Result: (1 + x^2)*ArcTan[x]/2 - x/2 *)

Int[x^2*ArcSin[x], x]
(* Result: ((-2 + x^2)*ArcSin[x])/3 + (x*Sqrt[1 - x^2])/3 *)
```

## Hyperbolic Functions

### Basic Hyperbolic Integrals

```mathematica
(* Basic hyperbolic functions *)
Int[Sinh[x], x]
(* Result: Cosh[x] *)

Int[Cosh[x], x]
(* Result: Sinh[x] *)

Int[Tanh[x], x]
(* Result: Log[Cosh[x]] *)

Int[Sech[x], x]
(* Result: ArcTan[Sinh[x]] *)

(* With linear arguments *)
Int[Sinh[a*x], x]
(* Result: Cosh[a*x]/a *)

Int[Cosh[a*x], x]
(* Result: Sinh[a*x]/a *)
```

### Powers and Products of Hyperbolic Functions

```mathematica
(* Hyperbolic powers *)
Int[Sinh[x]^2, x]
(* Result: -x/2 + Sinh[2*x]/4 *)

Int[Cosh[x]^2, x]
(* Result: x/2 + Sinh[2*x]/4 *)

Int[Tanh[x]^2, x]
(* Result: x - Tanh[x] *)

(* Products *)
Int[Sinh[x]*Cosh[x], x]
(* Result: Sinh[x]^2/2 *)

Int[x*Sinh[x], x]
(* Result: x*Cosh[x] - Sinh[x] *)
```

## Special Functions

### Error Functions and Related

```mathematica
(* Error function integrals *)
Int[Erf[x], x]
(* Result: x*Erf[x] + E^(-x^2)/Sqrt[π] *)

Int[x*Erf[x], x]
(* Result: (x^2*Erf[x])/2 + (x*E^(-x^2))/(2*Sqrt[π]) - Erf[x]/(4*Sqrt[π]) *)
```

### Gamma and Related Functions

```mathematica
(* Gamma function related integrals *)
Int[x^n*E^(-x), x]  (* Related to Gamma function *)
(* Various results depending on n *)
```

## Mixed Function Types

### Exponential-Trigonometric Combinations

```mathematica
(* Basic combinations *)
Int[E^x*Sin[x], x]
(* Result: E^x*(Sin[x] - Cos[x])/2 *)

Int[E^x*Cos[x], x]
(* Result: E^x*(Sin[x] + Cos[x])/2 *)

Int[E^(a*x)*Sin[b*x], x]
(* Result: E^(a*x)*(a*Sin[b*x] - b*Cos[b*x])/(a^2 + b^2) *)

(* More complex combinations *)
Int[x*E^x*Sin[x], x]
(* Result: (E^x*((-1 + x)*Sin[x] - (1 + x)*Cos[x]))/2 *)

Int[E^x*Sin[x]*Cos[x], x]
(* Result: E^x*(Sin[2*x] - 2*Cos[2*x])/10 *)
```

### Logarithmic-Trigonometric Combinations

```mathematica
(* Log-trig products *)
Int[Log[x]*Sin[x], x]
(* Complex expression involving special functions *)

Int[Sin[Log[x]], x]
(* Result: x*(Sin[Log[x]] - Cos[Log[x]])/2 *)

Int[Log[Sin[x]], x]
(* Result involves polylogarithms *)
```

### Polynomial-Transcendental Combinations

```mathematica
(* Complex mixed types *)
Int[x^2*E^x*Sin[x], x]
(* Result: E^x*((x^2 - 2)*Sin[x] - 2*x*Cos[x])/2 *)

Int[x*Log[x]*E^x, x]
(* Result: E^x*(-1 + x + x*Log[x]) *)

Int[ArcTan[x]/x^2, x]
(* Result: -ArcTan[x]/x + Log[1 + x^2]/2 *)
```

## Advanced Techniques

### Integration by Parts Examples

```mathematica
(* Classic integration by parts *)
Int[x*E^x, x]
(* Steps: u = x, dv = E^x dx *)
(* Result: E^x*(x - 1) *)

Int[ArcTan[x], x]
(* Steps: u = ArcTan[x], dv = dx *)
(* Result: x*ArcTan[x] - Log[1 + x^2]/2 *)

(* Multiple integration by parts *)
Int[x^2*E^x, x]
(* Result: E^x*(x^2 - 2*x + 2) *)
```

### Substitution Examples

```mathematica
(* Trigonometric substitutions *)
Int[1/Sqrt[1 - x^2], x]
(* Substitution: x = Sin[θ] *)
(* Result: ArcSin[x] *)

Int[1/(1 + x^2), x]
(* Substitution: x = Tan[θ] *)
(* Result: ArcTan[x] *)

(* Exponential substitutions *)
Int[E^x/(1 + E^x), x]
(* Substitution: u = E^x *)
(* Result: Log[1 + E^x] *)
```

### Partial Fractions

```mathematica
(* Automatic partial fraction decomposition *)
Int[1/((x - 1)*(x - 2)*(x - 3)), x]
(* Result: Log[x - 3]/2 - Log[x - 2] + Log[x - 1]/2 *)

Int[(x^2 + 1)/((x - 1)*(x + 1)*(x - 2)), x]
(* Complex partial fraction result *)
```

## Step-by-Step Examples

### Showing Integration Steps

```mathematica
(* Load with step capability *)
$LoadShowSteps = True;
Get["Rubi.m"]

(* Show first step only *)
Int[x*Sin[x], x, Step]
(* Shows: Integration by parts setup *)

(* Show all steps *)
Int[x*Sin[x], x, Steps]
(* Shows complete derivation *)

(* Show statistics *)
Int[x^2*E^x*Sin[x], x, Stats]
(* Returns: {steps, rules_used, input_size, output_size, ratio} *)
```

### Example Step-by-Step Output

For `Int[x*Sin[x], x, Steps]`:

```
Step 1: Apply integration by parts rule
   u = x, dv = Sin[x] dx
   du = dx, v = -Cos[x]
   
Step 2: Result = -x*Cos[x] - Int[-Cos[x], x]
   
Step 3: Integrate -Cos[x]
   Int[-Cos[x], x] = -Sin[x]
   
Final Result: -x*Cos[x] + Sin[x]
```

## Performance Comparison

### Rubi vs Built-in Integrate

```mathematica
(* Timing comparison *)
expr = x^3*E^x*Sin[x]*Cos[x];

(* Rubi timing *)
Timing[rubiResult = Int[expr, x]]

(* Built-in timing *)
Timing[mathematicaResult = Integrate[expr, x]]

(* Verify equivalence *)
Simplify[D[rubiResult, x] - expr] == 0
Simplify[D[mathematicaResult, x] - expr] == 0
```

### Complex Expression Benchmarks

```mathematica
(* Complex nested expression *)
complexExpr = x^2*Log[x]*ArcTan[x]*E^x;

(* Show integration statistics *)
Int[complexExpr, x, Stats]
(* Example output: {12, 8, 156, 298, 0.0513} *)
(* 12 steps, 8 rules, input size 156, output size 298, ratio 0.0513 *)
```

## Troubleshooting Common Issues

### When Integration Fails

```mathematica
(* Configure for unintegrable expressions *)
$Unintegrable = True;

Int[E^(x^2), x]
(* Returns: Unintegrable[E^(x^2), x] *)

(* Reset to default behavior *)
$Unintegrable = False;
Int[E^(x^2), x]
(* Returns: Int[E^(x^2), x] (unevaluated) *)
```

### Checking Results

```mathematica
(* Always verify by differentiation *)
result = Int[x^2*Sin[x], x];
D[result, x] == x^2*Sin[x]
(* Should return True *)

(* Simplify if needed *)
Simplify[D[result, x] - x^2*Sin[x]] == 0
```

---

*This comprehensive example guide demonstrates Rubi's capabilities across all major function types. For more advanced usage and rule development, see the [Developer Guide](DEVELOPMENT.md) and [API Reference](API.md).*