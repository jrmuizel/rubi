# Rubi File Structure and Organization

This document provides a detailed breakdown of Rubi's file structure, explaining the purpose, content, and organization of each file in the system. Understanding this structure is essential for navigating the codebase, contributing new rules, and maintaining the system.

## Table of Contents

- [Overview](#overview)
- [Core System Files](#core-system-files)
- [Integration Rule Files](#integration-rule-files)
- [Utility and Support Files](#utility-and-support-files)
- [File Naming Conventions](#file-naming-conventions)
- [Directory Organization](#directory-organization)
- [File Dependencies](#file-dependencies)
- [Loading Order](#loading-order)

## Overview

Rubi's file structure is organized around mathematical function types and integration techniques. The system consists of approximately 25 files, each containing related integration rules and supporting code. The organization follows a hierarchical structure from basic algebraic functions to complex transcendental functions.

### File Categories

1. **Core System Files**: Main package and build files
2. **Integration Rule Files**: Mathematical rule implementations
3. **Utility Files**: Helper functions and support code
4. **Documentation Files**: User and developer documentation

## Core System Files

### `Rubi.m`
**Purpose**: Main package file and entry point  
**Size**: ~149 lines  
**Key Components**:
- Package initialization and setup
- Function usage documentation
- Rule loading orchestration
- Global configuration management

**Key Functions**:
```mathematica
Int::usage          (* Main integration function documentation *)
Dist::usage         (* Distribution function documentation *)
Subst::usage        (* Substitution function documentation *)
LoadRules[filename] (* Rule file loading function *)
```

**Configuration Variables**:
- `$LoadShowSteps`: Enable step-by-step display
- `$Unintegrable`: Control unintegrable expression handling
- `$RuleColor`: Color for rule display
- `$ConditionColor`: Color for condition display

### `MakeRubiMxFile.m`
**Purpose**: Build script for creating compiled package  
**Size**: ~28 lines  
**Functionality**:
- Compiles Rubi into fast-loading MX format
- Supports both regular and step-display versions
- Handles cross-platform compatibility issues

**Usage**:
```mathematica
$LoadShowSteps = False;  (* Or True for step display *)
Get["MakeRubiMxFile.m"];
(* Creates Rubi.mx or StepRubi.mx *)
```

### `README`
**Purpose**: Basic project information  
**Size**: ~4 lines  
**Content**: Brief description and upstream repository link

## Integration Rule Files

### 1. Algebraic Function Rules

#### `1.1.1 Linear binomial products.m`
**Purpose**: Integration rules for linear binomial expressions  
**Size**: ~1,331 lines  
**Function Types Covered**:
- `(a + b*x)^m` - Basic binomial powers
- `(a + b*x)^m * (c + d*x)^n` - Binomial products
- `x^m * (a + b*x)^n` - Polynomial-binomial products

**Key Rule Examples**:
```mathematica
Int[x_^m_., x_Symbol] := x^(m+1)/(m+1) /; FreeQ[m,x] && NeQ[m,-1]
Int[(a_.+b_.*x_)^m_, x_Symbol] := (a+b*x)^(m+1)/(b*(m+1)) /; FreeQ[{a,b,m},x] && NeQ[m,-1]
```

#### `1.1.2 Quadratic binomial products.m`
**Purpose**: Special cases of quadratic binomial products  
**Size**: ~141 lines  
**Specialization**: Optimized rules for specific quadratic cases

#### `1.1.3 General binomial products.m`
**Purpose**: General binomial product integration  
**Size**: ~2,583 lines  
**Coverage**: Most comprehensive binomial rule set  
**Includes**: Complex polynomial-binomial combinations

#### `1.1.4 Improper binomial products.m`
**Purpose**: Edge cases and special conditions for binomials  
**Size**: ~628 lines  
**Handles**: Degenerate cases, boundary conditions, special values

#### `1.2.1 Quadratic trinomial products.m`
**Purpose**: Quadratic trinomial expressions  
**Size**: ~3,585 lines  
**Function Types**: `x^m * (a + b*x + c*x^2)^n`  
**Techniques**: Discriminant analysis, completing the square

#### `1.2.2 Quartic trinomial products.m`
**Purpose**: Higher-degree trinomial expressions  
**Size**: ~1,958 lines  
**Specialization**: Fourth-degree and related expressions

#### `1.2.3 General trinomial products.m`
**Purpose**: General trinomial integration rules  
**Size**: ~2,420 lines  
**Coverage**: Comprehensive trinomial rule set

#### `1.2.4 Improper trinomial products.m`
**Purpose**: Trinomial edge cases and special conditions  
**Size**: ~465 lines  
**Handles**: Degenerate trinomials, special parameter values

#### `1.3 Miscellaneous algebraic functions.m`
**Purpose**: Other algebraic function patterns  
**Size**: ~669 lines  
**Includes**: Radical expressions, nested algebraic functions

### 2. Transcendental Function Rules

#### `2 Exponentials.m`
**Purpose**: Exponential function integration  
**Size**: ~723 lines  
**Function Types**:
- `F^(g*(e + f*x))` - General exponential forms
- `(c + d*x)^m * F^(g*(e + f*x))` - Polynomial-exponential products
- Mixed exponential expressions

**Key Patterns**:
```mathematica
Int[F_^(g_.*(e_.+f_.*x_)), x_Symbol] := F^(g*(e+f*x))/(f*g*Log[F])
Int[x_^m_*F_^(g_.*(e_.+f_.*x_)), x_Symbol] := (* Integration by parts *)
```

#### `3 Logarithms.m`
**Purpose**: Logarithmic function integration  
**Size**: ~1,554 lines  
**Function Types**:
- `Log[a + b*x]` - Basic logarithms
- `x^m * Log[a + b*x]` - Polynomial-logarithmic products
- `Log[complex_expression]` - Complex logarithmic arguments

### 3. Trigonometric Function Rules

#### `4.1 Sine.m`
**Purpose**: Sine function integration rules  
**Size**: ~5,623 lines (largest rule file)  
**Coverage**:
- Basic sine integrals
- Sine powers: `Sin[x]^n`
- Polynomial-sine products: `x^m * Sin[a + b*x]`
- Complex sine expressions

#### `4.2 Tangent.m`
**Purpose**: Tangent function integration  
**Size**: ~1,893 lines  
**Includes**: Tangent powers, tangent products, rational tangent expressions

#### `4.3 Secant.m`
**Purpose**: Secant function integration  
**Size**: ~2,682 lines  
**Specialization**: Secant and cosecant function rules

#### `4.4 Miscellaneous trig functions.m`
**Purpose**: Other trigonometric patterns  
**Size**: ~2,503 lines  
**Includes**: Mixed trigonometric functions, complex combinations

### 4. Inverse and Hyperbolic Functions

#### `5 Inverse trig functions.m`
**Purpose**: Inverse trigonometric function integration  
**Size**: ~4,218 lines  
**Functions**: ArcSin, ArcCos, ArcTan, ArcSec, ArcCsc, ArcCot

#### `6 Hyperbolic functions.m`
**Purpose**: Hyperbolic function integration  
**Size**: ~2,220 lines  
**Functions**: Sinh, Cosh, Tanh, Sech, Csch, Coth

#### `7 Inverse hyperbolic functions.m`
**Purpose**: Inverse hyperbolic function integration  
**Size**: ~4,473 lines  
**Functions**: ArcSinh, ArcCosh, ArcTanh, ArcSech, ArcCsch, ArcCoth

#### `8 Special functions.m`
**Purpose**: Special mathematical functions  
**Size**: ~1,855 lines  
**Includes**: Error functions, Gamma functions, Bessel functions

### 5. Meta-Rules and Utilities

#### `9.1 Integrand simplification rules.m`
**Purpose**: Pre-processing and simplification  
**Size**: ~310 lines  
**Function**: Simplify integrands before applying integration rules

#### `9.2 Derivative integration rules.m`
**Purpose**: Integration of derivatives  
**Size**: ~161 lines  
**Handles**: Expressions involving derivatives

#### `9.3 Piecewise linear functions.m`
**Purpose**: Piecewise function integration  
**Size**: ~197 lines  
**Handles**: Step functions, piecewise linear expressions

#### `9.4 Miscellaneous integration rules.m`
**Purpose**: Cleanup and fallback rules  
**Size**: ~624 lines  
**Function**: Final transformation rules, general patterns

## Utility and Support Files

### `Integration Utility Functions.m`
**Purpose**: Core utility functions for rule conditions  
**Size**: ~8,008 lines (largest file)  
**Categories**:

#### Mathematical Testing Functions
```mathematica
FreeQ[expr, var]        (* Variable independence testing *)
IntegerQ[n]             (* Integer testing *)
RationalQ[n]            (* Rational number testing *)
ComplexNumberQ[n]       (* Complex number testing *)
```

#### Structure Testing Functions
```mathematica
PowerQ[expr]            (* Power expression testing *)
ProductQ[expr]          (* Product expression testing *)
SumQ[expr]              (* Sum expression testing *)
LogQ[expr]              (* Logarithm testing *)
TrigQ[expr]             (* Trigonometric function testing *)
```

#### Comparison Functions
```mathematica
EqQ[u, v]               (* Equality testing *)
GtQ[u, v]               (* Greater than testing *)
IGtQ[u, n]              (* Integer greater than testing *)
```

### `ShowStep Routines.m`
**Purpose**: Step-by-step integration display  
**Size**: ~282 lines  
**Key Components**:
- Step tracking and display
- Rule application visualization
- Statistics collection
- Color-coded output

**Key Functions**:
```mathematica
StepFunction[func]      (* Modify rules for step display *)
Int[expr, var, Step]    (* Show first step *)
Int[expr, var, Steps]   (* Show all steps *)
Int[expr, var, Stats]   (* Show statistics *)
```

### `Rubi4.15.nb`
**Purpose**: Mathematica notebook with examples and documentation  
**Size**: ~656 lines  
**Content**: Interactive examples, installation instructions, usage demonstrations

## File Naming Conventions

### Numerical Prefixes
- `1.x.x`: Algebraic functions
  - `1.1.x`: Binomial products
  - `1.2.x`: Trinomial products
  - `1.3`: Miscellaneous algebraic
- `2`: Exponential functions
- `3`: Logarithmic functions
- `4.x`: Trigonometric functions
  - `4.1`: Sine
  - `4.2`: Tangent
  - `4.3`: Secant
  - `4.4`: Miscellaneous trig
- `5`: Inverse trigonometric
- `6`: Hyperbolic functions
- `7`: Inverse hyperbolic
- `8`: Special functions
- `9.x`: Meta-rules and utilities

### Function Type Descriptors
- `Linear binomial products`: `(a + b*x)` expressions
- `Quadratic trinomial products`: `(a + b*x + c*x^2)` expressions
- `General`: Comprehensive rule sets
- `Improper`: Edge cases and special conditions
- `Miscellaneous`: Mixed or uncategorized patterns

## Directory Organization

```
rubi/
├── README.md                           # Main documentation
├── docs/                              # Documentation directory
│   ├── API.md                         # API reference
│   ├── RULES.md                       # Rule system guide
│   ├── EXAMPLES.md                    # Usage examples
│   ├── DEVELOPMENT.md                 # Developer guide
│   └── STRUCTURE.md                   # This file
├── Rubi.m                             # Main package
├── MakeRubiMxFile.m                   # Build script
├── Integration Utility Functions.m    # Utility functions
├── ShowStep Routines.m                # Step display
├── Rubi4.15.nb                       # Example notebook
├── README                             # Basic project info
└── [Rule Files]                       # Integration rule files
    ├── 1.1.1 Linear binomial products.m
    ├── 1.1.2 Quadratic binomial products.m
    ├── 1.1.3 General binomial products.m
    ├── 1.1.4 Improper binomial products.m
    ├── 1.2.1 Quadratic trinomial products.m
    ├── 1.2.2 Quartic trinomial products.m
    ├── 1.2.3 General trinomial products.m
    ├── 1.2.4 Improper trinomial products.m
    ├── 1.3 Miscellaneous algebraic functions.m
    ├── 2 Exponentials.m
    ├── 3 Logarithms.m
    ├── 4.1 Sine.m
    ├── 4.2 Tangent.m
    ├── 4.3 Secant.m
    ├── 4.4 Miscellaneous trig functions.m
    ├── 5 Inverse trig functions.m
    ├── 6 Hyperbolic functions.m
    ├── 7 Inverse hyperbolic functions.m
    ├── 8 Special functions.m
    ├── 9.1 Integrand simplification rules.m
    ├── 9.2 Derivative integration rules.m
    ├── 9.3 Piecewise linear functions.m
    └── 9.4 Miscellaneous integration rules.m
```

## File Dependencies

### Core Dependencies
```
Rubi.m
├── Integration Utility Functions.m    (always loaded first)
├── 9.1 Integrand simplification rules.m
├── [Algebraic Rule Files 1.x.x]
├── [Transcendental Rule Files 2-8] (conditional)
├── 9.4 Miscellaneous integration rules.m
└── ShowStep Routines.m (conditional)
```

### Dependency Chain
1. **Integration Utility Functions.m** - Must be loaded first (provides all utility functions)
2. **9.1 Integrand simplification rules.m** - Pre-processing rules
3. **Algebraic rule files (1.x.x)** - Always loaded, order matters for specificity
4. **Transcendental rule files (2-8)** - Conditionally loaded based on `$LoadElementaryFunctionRules`
5. **9.4 Miscellaneous integration rules.m** - Cleanup rules, loaded last
6. **ShowStep Routines.m** - Conditionally loaded based on `$LoadShowSteps`

### Internal File Dependencies
- All rule files depend on **Integration Utility Functions.m**
- Step display files require **ShowStep Routines.m**
- Some rule files may reference functions defined in other rule files

## Loading Order

The loading order in `Rubi.m` is carefully designed for optimal performance and rule precedence:

```mathematica
(* 1. Core utilities - always first *)
LoadRules["Integration utility functions"];

(* 2. Pre-processing rules *)
LoadRules["9.1 Integrand simplification rules"];

(* 3. Algebraic functions - most specific to general *)
LoadRules["1.1.1 Linear binomial products"];
LoadRules["1.1.3 General binomial products"];
LoadRules["1.2.1 Quadratic trinomial products"];
LoadRules["1.1.2 Quadratic binomial products"];
LoadRules["1.2.2 Quartic trinomial products"];
LoadRules["1.2.3 General trinomial products"];
LoadRules["1.2.4 Improper trinomial products"];
LoadRules["1.1.4 Improper binomial products"];
LoadRules["1.3 Miscellaneous algebraic functions"];

(* 4. Transcendental functions - conditional loading *)
If[Global`$LoadElementaryFunctionRules===True,
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
];

(* 5. Cleanup rules - always last *)
LoadRules["9.4 Miscellaneous integration rules"];

(* 6. Step display setup - conditional *)
If[$LoadShowSteps===True, 
  LoadRules["ShowStep routines"];
  StepFunction[Int];
];
```

### Loading Order Rationale

1. **Utilities First**: All rule files depend on utility functions
2. **Simplification Early**: Pre-process integrands for optimal rule matching
3. **Specific to General**: More specific rules should be tried first
4. **Function Type Grouping**: Related function types loaded together
5. **Conditional Loading**: Transcendental functions optional for basic usage
6. **Cleanup Last**: General rules that should only apply if nothing else matches
7. **Step Display Final**: Modifies all loaded rules, so must come last

## File Modification Guidelines

### Adding New Rules
1. **Identify appropriate file** based on function type
2. **Place rules in order of specificity** (specific patterns first)
3. **Follow existing formatting** and documentation conventions
4. **Update file size estimates** in this documentation
5. **Test thoroughly** before committing

### Creating New Files
1. **Follow naming convention** (numerical prefix + descriptive name)
2. **Add to loading sequence** in `Rubi.m`
3. **Include proper file header** with title, purpose, and metadata
4. **Document in this structure guide**
5. **Update dependency information**

### File Maintenance
1. **Keep size manageable** (split large files when necessary)
2. **Maintain consistent organization** within files
3. **Document major changes** in file headers
4. **Update cross-references** when moving rules between files

---

*This file structure documentation provides the foundation for understanding and navigating Rubi's codebase. For specific implementation details, consult the [Developer Guide](DEVELOPMENT.md) and individual source files.*