# Rubi Integration Rules System

This document explains the comprehensive rule-based system that powers Rubi's symbolic integration capabilities. Understanding this system is crucial for users who want to extend Rubi or understand how it works internally.

## Table of Contents

- [Rule System Overview](#rule-system-overview)
- [Rule Organization](#rule-organization)
- [Rule File Structure](#rule-file-structure)
- [Rule Syntax and Patterns](#rule-syntax-and-patterns)
- [Rule Categories](#rule-categories)
- [Rule Application Process](#rule-application-process)
- [Extending the Rule System](#extending-the-rule-system)

## Rule System Overview

Rubi (Rule-Based Integrator) uses over 6,000 carefully crafted integration rules to compute symbolic antiderivatives. Unlike traditional algorithmic approaches, Rubi's rule-based system:

- **Matches patterns** in the integrand to select appropriate integration techniques
- **Applies transformations** systematically to reduce complex integrals to simpler forms
- **Ensures mathematical correctness** through rigorous rule validation
- **Provides transparency** by showing the steps used in integration

### Key Principles

1. **Pattern Matching**: Each rule defines a pattern that matches specific types of integrands
2. **Condition Testing**: Rules include conditions that must be satisfied for application
3. **Hierarchical Organization**: Rules are organized from specific to general cases
4. **Recursive Application**: Complex integrals are broken down through rule chains

## Rule Organization

Rubi's rules are organized into multiple files based on the types of functions involved:

### 1. Algebraic Functions
- **1.1.1 Linear binomial products.m**: `(a + b*x)^m` type expressions
- **1.1.2 Quadratic binomial products.m**: Special quadratic cases
- **1.1.3 General binomial products.m**: `x^m*(a + b*x)^n` type expressions  
- **1.1.4 Improper binomial products.m**: Edge cases and special conditions
- **1.2.1 Quadratic trinomial products.m**: `x^m*(a + b*x + c*x^2)^n` expressions
- **1.2.2 Quartic trinomial products.m**: Higher degree trinomials
- **1.2.3 General trinomial products.m**: General trinomial patterns
- **1.2.4 Improper trinomial products.m**: Special trinomial cases
- **1.3 Miscellaneous algebraic functions.m**: Other algebraic patterns

### 2. Transcendental Functions
- **2 Exponentials.m**: Exponential function rules
- **3 Logarithms.m**: Logarithmic function rules

### 3. Trigonometric Functions
- **4.1 Sine.m**: Sine function integration rules
- **4.2 Tangent.m**: Tangent function integration rules
- **4.3 Secant.m**: Secant function integration rules
- **4.4 Miscellaneous trig functions.m**: Other trigonometric patterns

### 4. Inverse and Hyperbolic Functions
- **5 Inverse trig functions.m**: Inverse trigonometric functions
- **6 Hyperbolic functions.m**: Hyperbolic function rules
- **7 Inverse hyperbolic functions.m**: Inverse hyperbolic functions
- **8 Special functions.m**: Other special mathematical functions

### 5. Meta-Rules and Utilities
- **9.1 Integrand simplification rules.m**: Pre-processing rules
- **9.2 Derivative integration rules.m**: Rules for derivatives
- **9.3 Piecewise linear functions.m**: Piecewise function handling
- **9.4 Miscellaneous integration rules.m**: General utility rules

## Rule File Structure

Each rule file follows a consistent structure using Mathematica's package format:

```mathematica
(* ::Package:: *)

(* ::Section:: *)
(*Rule Category Name*)

(* ::Subsection::Closed:: *)
(*Specific Rule Subsection*)

Int[pattern_, x_Symbol] :=
  result /;
condition1 && condition2 && ...
```

### Example Rule Structure

```mathematica
(* Basic power rule *)
Int[x_^m_., x_Symbol] :=
  x^(m+1)/(m+1) /;
FreeQ[m,x] && NeQ[m,-1]

(* Linear binomial rule *)
Int[(a_.+b_.*x_)^m_, x_Symbol] :=
  (a+b*x)^(m+1)/(b*(m+1)) /;
FreeQ[{a,b,m},x] && NeQ[m,-1]
```

### Rule Components

1. **Pattern**: `Int[pattern_, x_Symbol]` - Defines what integrands match
2. **Result**: The antiderivative expression 
3. **Conditions**: `/; condition1 && condition2` - Requirements for rule application

## Rule Syntax and Patterns

### Pattern Matching Syntax

- `x_`: Matches any expression, names it `x`
- `x_Symbol`: Matches only symbols, names it `x`
- `a_.`: Optional pattern with default value
- `a_.*x_`: Matches `a*x` where `a` is optional (default 1)
- `(expr_)^m_.`: Matches powers with optional exponent (default 1)

### Common Pattern Examples

```mathematica
(* Polynomial patterns *)
x_^m_.                          (* x^m where m is optional *)
a_.+b_.*x_                      (* a + b*x with optional coefficients *)
(a_.+b_.*x_)^m_.               (* (a + b*x)^m *)

(* Function patterns *)
F_^(g_.*(e_.+f_.*x_))          (* F^(g*(e + f*x)) for exponentials *)
Sin[a_.+b_.*x_]                 (* Sin[a + b*x] for trigonometric *)
Log[a_.+b_.*x_]                 (* Log[a + b*x] for logarithmic *)
```

### Condition Testing Functions

Rubi uses many specialized testing functions in rule conditions:

- `FreeQ[expr, x]`: Test if expression is free of variable x
- `IntegerQ[n]`: Test if n is an integer
- `RationalQ[n]`: Test if n is a rational number
- `GtQ[a, b]`: Test if a > b
- `EqQ[a, b]`: Test if a equals b
- `TrigQ[expr]`: Test if expression is trigonometric

## Rule Categories

### 1. Basic Algebraic Rules

**Power Rules**: Handle polynomial and rational expressions
```mathematica
Int[x_^m_, x_Symbol] := x^(m+1)/(m+1) /; FreeQ[m,x] && NeQ[m,-1]
Int[1/x_, x_Symbol] := Log[x]
```

**Binomial Rules**: Handle expressions like `(a + b*x)^m`
```mathematica
Int[(a_.+b_.*x_)^m_, x_Symbol] := 
  (a+b*x)^(m+1)/(b*(m+1)) /; FreeQ[{a,b,m},x] && NeQ[m,-1]
```

### 2. Transcendental Function Rules

**Exponential Rules**: Handle exponential functions and combinations
```mathematica
Int[F_^(g_.*(e_.+f_.*x_)), x_Symbol] := 
  F^(g*(e+f*x))/(f*g*Log[F]) /; FreeQ[{F,e,f,g},x]
```

**Logarithmic Rules**: Handle logarithmic expressions
```mathematica
Int[Log[a_.+b_.*x_], x_Symbol] := 
  (a+b*x)*Log[a+b*x]/b - x /; FreeQ[{a,b},x]
```

### 3. Trigonometric Function Rules

**Basic Trig Rules**: Standard trigonometric integrals
```mathematica
Int[Sin[a_.+b_.*x_], x_Symbol] := -Cos[a+b*x]/b /; FreeQ[{a,b},x]
Int[Cos[a_.+b_.*x_], x_Symbol] := Sin[a+b*x]/b /; FreeQ[{a,b},x]
```

**Product Rules**: Handle products of trigonometric functions
```mathematica
Int[Sin[a_.+b_.*x_]*Cos[c_.+d_.*x_], x_Symbol] := ...
```

### 4. Reduction Rules

**Integration by Parts**: Automated integration by parts
```mathematica
Int[x_^m_.*Log[a_.+b_.*x_], x_Symbol] := 
  x^(m+1)*Log[a+b*x]/(m+1) - b/(m+1)*Int[x^(m+1)/(a+b*x), x] /; ...
```

**Substitution Rules**: Systematic substitutions
```mathematica
Int[(a_.+b_.*u_)^m_, x_Symbol] := 
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m,x], x, u] /; ...
```

## Rule Application Process

### 1. Pattern Matching Phase
- Rubi searches through rules in order of specificity
- Most specific patterns are tested first
- First matching pattern with satisfied conditions is used

### 2. Condition Evaluation
- All conditions in the rule must evaluate to `True`
- Conditions check mathematical properties and constraints
- Failed conditions cause rule to be skipped

### 3. Transformation Application
- Rule right-hand side is evaluated
- May involve recursive calls to `Int[]`
- May involve calls to utility functions like `Dist[]` or `Subst[]`

### 4. Simplification
- Result is automatically simplified
- Common subexpressions are consolidated
- Mathematical identities are applied

### Example Rule Application

For `Int[x*Sin[x], x]`:

1. **Pattern Match**: Matches rule for `x^m*Sin[a + b*x]` with `m=1`, `a=0`, `b=1`
2. **Condition Check**: Verifies `m` is integer, `a,b` are free of `x`
3. **Apply Integration by Parts**: 
   ```mathematica
   -x*Cos[x] + Int[Cos[x], x]
   ```
4. **Recursive Integration**: `Int[Cos[x], x]` → `Sin[x]`
5. **Final Result**: `-x*Cos[x] + Sin[x]`

## Extending the Rule System

### Adding New Rules

1. **Identify the Pattern**: Determine the type of integrand
2. **Choose Appropriate File**: Add to the relevant rule category file
3. **Write the Rule**: Follow the established syntax and conventions
4. **Add Conditions**: Ensure proper condition testing
5. **Test Thoroughly**: Verify the rule works correctly

### Rule Development Guidelines

1. **Specificity**: More specific rules should come before general ones
2. **Conditions**: Include all necessary mathematical constraints
3. **Efficiency**: Prefer direct results over complex recursive chains
4. **Correctness**: Verify mathematical validity of transformations

### Example New Rule

```mathematica
(* New rule for integrating x^2*Sin[x] *)
Int[x_^2*Sin[a_.+b_.*x_], x_Symbol] :=
  -x^2*Cos[a+b*x]/b + 2/b*Int[x*Cos[a+b*x], x] /;
FreeQ[{a,b},x]
```

### Testing New Rules

```mathematica
(* Test the new rule *)
test1 = Int[x^2*Sin[x], x]
test2 = Int[x^2*Sin[2*x], x]  
test3 = Int[x^2*Sin[x + Pi/4], x]

(* Verify by differentiation *)
D[test1, x] == x^2*Sin[x]
```

## Advanced Rule Features

### Meta-Rules
Rules that operate on other rules or control rule application:
- Simplification rules that preprocess integrands
- Distribution rules that factor out constants
- Substitution rules that change variables

### Conditional Loading
Some rule sets are only loaded under specific conditions:
```mathematica
If[Global`$LoadElementaryFunctionRules===True,
  LoadRules["2 Exponentials"];
  LoadRules["3 Logarithms"];
  (* ... other transcendental function rules *)
]
```

### Rule Priorities
Rules are applied in order of appearance, allowing fine control over which transformation is used first.

---

*This rule system documentation provides the foundation for understanding and extending Rubi's integration capabilities. For specific implementation details, consult the individual rule files and the [Developer Guide](DEVELOPMENT.md).*