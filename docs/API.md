# Rubi API Reference

This document provides complete reference documentation for all functions, symbols, and configuration options in Rubi (Rule-Based Integrator).

## Table of Contents

- [Core Integration Functions](#core-integration-functions)
- [Configuration Variables](#configuration-variables)
- [Utility Functions](#utility-functions)
- [Step Display Functions](#step-display-functions)
- [Mathematical Testing Functions](#mathematical-testing-functions)
- [Comparison Functions](#comparison-functions)
- [Inert Functions](#inert-functions)

## Core Integration Functions

### `Int[expr, var]`

**Description**: Main integration function that computes the antiderivative (indefinite integral) of an expression.

**Parameters**:
- `expr`: Mathematical expression to integrate
- `var`: Variable of integration (must be a Symbol)

**Returns**: Antiderivative of `expr` with respect to `var`

**Examples**:
```mathematica
Int[x^2, x]                    (* Returns: x^3/3 *)
Int[Sin[x], x]                 (* Returns: -Cos[x] *)
Int[E^x * Cos[x], x]          (* Returns: (E^x*(Cos[x] + Sin[x]))/2 *)
```

### `Int[expr, var, flag]`

**Description**: Extended integration function with additional display or analysis options.

**Parameters**:
- `expr`: Mathematical expression to integrate
- `var`: Variable of integration
- `flag`: One of `Step`, `Steps`, or `Stats`

**Flags**:
- `Step`: Display the first integration step and return intermediate result
- `Steps`: Display all integration steps and return final result
- `Stats`: Display integration statistics and return result

**Examples**:
```mathematica
Int[x*Sin[x], x, Step]         (* Shows first step *)
Int[x*Sin[x], x, Steps]        (* Shows all steps *)
Int[x*Sin[x], x, Stats]        (* Shows {steps, rules, input_size, output_size, ratio} *)
```

### `Int[{expr1, expr2, ...}, var]`

**Description**: Integrate multiple expressions simultaneously.

**Parameters**:
- `{expr1, expr2, ...}`: List of expressions to integrate
- `var`: Variable of integration

**Returns**: List of antiderivatives

**Example**:
```mathematica
Int[{x^2, Sin[x], 1/(1+x^2)}, x]  (* Returns: {x^3/3, -Cos[x], ArcTan[x]} *)
```

### `Int[expr, {var, a, b}]`

**Description**: Compute definite integral (limits of antiderivative).

**Parameters**:
- `expr`: Expression to integrate
- `{var, a, b}`: Variable and integration limits

**Returns**: `Limit[antiderivative, var->b] - Limit[antiderivative, var->a]`

**Note**: This may not always equal the definite integral if the function has discontinuities.

**Example**:
```mathematica
Int[x^2, {x, 0, 1}]           (* Returns: 1/3 *)
```

### `Dist[factor, expr, var]`

**Description**: Distribute a factor over an expression during integration.

**Parameters**:
- `factor`: Factor to distribute
- `expr`: Expression to distribute over
- `var`: Variable of integration

**Usage**: Internal function used by integration rules for distributing constants and simple factors.

### `Subst[expr, var, value]`

**Description**: Substitute a value for a variable in an expression.

**Parameters**:
- `expr`: Expression containing the variable
- `var`: Variable to substitute
- `value`: Value to substitute

**Returns**: Expression with `var` replaced by `value`

## Configuration Variables

### `$Unintegrable`

**Type**: Boolean  
**Default**: `False`

**Description**: Controls behavior when expressions cannot be integrated in closed form.

- `True`: Return `Unintegrable[expr, var]` for non-integrable expressions
- `False`: Return `Int[expr, var]` (unevaluated) for non-integrable expressions

**Example**:
```mathematica
$Unintegrable = True;
Int[E^(x^2), x]               (* Returns: Unintegrable[E^(x^2), x] *)
```

### `$RuleColor`

**Type**: Color specification  
**Default**: `Red`

**Description**: Color used to display integration rules when showing steps.

**Example**:
```mathematica
$RuleColor = Blue;            (* Rules will display in blue *)
```

### `$ConditionColor`

**Type**: Color specification  
**Default**: `Blue`

**Description**: Color used to display rule application conditions when showing steps.

**Example**:
```mathematica
$ConditionColor = Green;      (* Conditions will display in green *)
```

### `$StepCounter`

**Type**: Integer  
**Default**: `0`

**Description**: Counter incremented each time an integration rule is applied (when ShowSteps is loaded).

### `$LoadShowSteps`

**Type**: Boolean  
**Default**: `False`

**Description**: Whether to load step-by-step integration display functionality.

**Usage**: Set before loading Rubi or compiling with `MakeRubiMxFile.m`.

## Utility Functions

### Mathematical Testing Functions

#### `FreeQ[expr, var]`
Test if expression is free of a variable.

#### `RationalQ[expr]`
Test if expression is a rational number.

#### `IntegerQ[expr]`
Test if expression is an integer.

#### `IntegersQ[m, n, ...]`
Test if all arguments are explicit integers.

#### `HalfIntegerQ[expr]`
Test if expression is a half-integer (n/2 where n is odd integer).

#### `FractionQ[expr]`
Test if expression is an explicit fraction.

#### `ComplexNumberQ[expr]`
Test if expression is an explicit complex number.

#### `RealNumberQ[expr]`
Test if expression is an explicit real (non-complex) number.

#### `FractionOrNegativeQ[expr]`
Test if expression is a fraction or negative number.

#### `SqrtNumberQ[expr]`
Test if expression is equivalent to the square root of a rational number.

#### `SqrtNumberSumQ[expr]`
Test if expression is equivalent to a sum of square-root numbers.

### Structure Testing Functions

#### `PowerQ[expr]`
Test if expression is a power (form `base^exponent`).

#### `ProductQ[expr]`
Test if expression is a product.

#### `SumQ[expr]`
Test if expression is a sum.

#### `NonsumQ[expr]`
Test if expression is not a sum.

#### `IntegerPowerQ[expr]`
Test if expression is an integer power.

#### `FractionalPowerQ[expr]`
Test if expression is a fractional power.

#### `FractionalPowerFreeQ[expr]`
Test if expression is free of fractional powers (except atomic bases).

#### `ComplexFreeQ[expr]`
Test if expression is free of complex numbers.

### Function Type Testing

#### `LogQ[expr]`
Test if expression is of the form `Log[v]`.

#### `TrigQ[expr]`
Test if expression is a circular trigonometric function.

#### `HyperbolicQ[expr]`
Test if expression is a hyperbolic function.

#### `InverseTrigQ[expr]`
Test if expression is an inverse circular trigonometric function.

#### `InverseHyperbolicQ[expr]`
Test if expression is an inverse hyperbolic function.

## Comparison Functions

### `EqQ[u, v]`
Test if `u - v` equals zero.

### `NeQ[u, v]`
Test if `u - v` does not equal zero.

### Integer Comparisons

#### `IGtQ[u, n]`
Test if `u` is an integer and `u > n`.

#### `ILtQ[u, n]`
Test if `u` is an integer and `u < n`.

#### `IGeQ[u, n]`
Test if `u` is an integer and `u >= n`.

#### `ILeQ[u, n]`
Test if `u` is an integer and `u <= n`.

### General Comparisons

#### `GtQ[u, v]`
Test if `u > v`.

#### `LtQ[u, v]`
Test if `u < v`.

#### `GeQ[u, v]`
Test if `u >= v`.

#### `LeQ[u, v]`
Test if `u <= v`.

## Step Display Functions

### `Step`
Symbol used as flag in `Int[expr, var, Step]` to display first integration step.

### `Steps`
Symbol used as flag in `Int[expr, var, Steps]` to display all integration steps.

### `Stats`
Symbol used as flag in `Int[expr, var, Stats]` to display integration statistics.

The statistics returned are in the form `{a, b, c, d, e}` where:
- `a`: Number of steps used to integrate the expression
- `b`: Number of distinct rules used
- `c`: Leaf count size of the input expression
- `d`: Leaf count size of the antiderivative
- `e`: Rule-to-size ratio (quotient of `b` and `c`)

## Special Return Values

### `Unintegrable[expr, var]`
Indicates that `expr` is not integrable with respect to `var` in closed form using the functions Rubi recognizes.

### `CannotIntegrate[expr, var]`
Indicates that Rubi is unable to integrate `expr` with respect to `var`, though it might be integrable.

## Inert Functions

Rubi defines inert versions of trigonometric functions to avoid automatic evaluation during rule application:

### `sin[x]`
Inert sine function

### `cos[x]`
Inert cosine function

### `tan[x]`
Inert tangent function

### `cot[x]`
Inert cotangent function

### `sec[x]`
Inert secant function

### `csc[x]`
Inert cosecant function

These are used internally by the integration rules and are automatically converted to standard Mathematica functions in the final result.

## Usage Examples

### Basic Integration
```mathematica
(* Load Rubi *)
Get["Rubi.m"]

(* Simple integrations *)
Int[x^3, x]
Int[Sin[x]*Cos[x], x]
Int[1/(1 + x^2), x]
```

### Step-by-Step Analysis
```mathematica
(* Load with step support *)
$LoadShowSteps = True;
Get["Rubi.m"]

(* Show integration process *)
Int[x*E^x, x, Steps]
Int[x^2*Sin[x], x, Stats]
```

### Advanced Usage
```mathematica
(* Configure behavior *)
$Unintegrable = True;
$RuleColor = Purple;

(* Test mathematical properties *)
result = Int[x*Log[x], x];
If[ComplexFreeQ[result], Print["Result is real"], Print["Result is complex"]]
```

---

*This API reference covers all major functions and features in Rubi. For implementation details and rule development, see the [Developer Guide](DEVELOPMENT.md).*