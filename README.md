# Rubi - Rule-Based Integrator

[![Mathematica](https://img.shields.io/badge/Mathematica-compatible-red.svg)](https://www.wolfram.com/mathematica/)
[![License](https://img.shields.io/badge/license-Custom-blue.svg)](LICENSE)

**Rubi** (Rule-Based Integrator) is a comprehensive symbolic integration package for Wolfram Mathematica, developed by Albert D. Rich. It uses a large collection of carefully crafted rules to compute antiderivatives of mathematical expressions with high accuracy and efficiency.

## 🌟 Features

- **Comprehensive Rule System**: Over 6,000 integration rules covering:
  - Algebraic functions (linear, quadratic, general binomials and trinomials)
  - Transcendental functions (exponentials, logarithms)
  - Trigonometric and hyperbolic functions
  - Inverse trigonometric and hyperbolic functions
  - Special functions
  - Mixed expressions

- **Step-by-Step Integration**: Display detailed integration steps for educational purposes
- **Performance Statistics**: Monitor integration complexity and rule usage
- **Extensible Architecture**: Well-organized rule system for easy extension
- **Robust Utility Functions**: Comprehensive set of helper functions for pattern matching and manipulation

## 📁 Project Structure

```
rubi/
├── README.md                                    # This file
├── Rubi.m                                      # Main package file
├── MakeRubiMxFile.m                           # Build script for compiled package
├── ShowStep Routines.m                        # Step-by-step display functionality
├── Integration Utility Functions.m            # Core utility functions
├── Rubi4.15.nb                               # Mathematica notebook with examples
├── 1.1.1 Linear binomial products.m          # Linear binomial integration rules
├── 1.1.2 Quadratic binomial products.m       # Quadratic binomial integration rules
├── 1.1.3 General binomial products.m         # General binomial integration rules
├── 1.1.4 Improper binomial products.m        # Improper binomial integration rules
├── 1.2.1 Quadratic trinomial products.m      # Quadratic trinomial integration rules
├── 1.2.2 Quartic trinomial products.m        # Quartic trinomial integration rules
├── 1.2.3 General trinomial products.m        # General trinomial integration rules
├── 1.2.4 Improper trinomial products.m       # Improper trinomial integration rules
├── 1.3 Miscellaneous algebraic functions.m   # Miscellaneous algebraic rules
├── 2 Exponentials.m                           # Exponential function rules
├── 3 Logarithms.m                             # Logarithmic function rules
├── 4.1 Sine.m                                 # Sine function rules
├── 4.2 Tangent.m                              # Tangent function rules
├── 4.3 Secant.m                               # Secant function rules
├── 4.4 Miscellaneous trig functions.m        # Other trigonometric rules
├── 5 Inverse trig functions.m                 # Inverse trigonometric rules
├── 6 Hyperbolic functions.m                   # Hyperbolic function rules
├── 7 Inverse hyperbolic functions.m          # Inverse hyperbolic rules
├── 8 Special functions.m                      # Special function rules
├── 9.1 Integrand simplification rules.m      # Simplification rules
├── 9.2 Derivative integration rules.m        # Derivative-based rules
├── 9.3 Piecewise linear functions.m          # Piecewise function rules
└── 9.4 Miscellaneous integration rules.m     # Additional miscellaneous rules
```

## 🚀 Installation

### Method 1: Direct Loading (Recommended for Development)

1. **Download or clone** this repository to your local machine
2. **Place all files** in a directory accessible to Mathematica
3. **Load the package** in Mathematica:

```mathematica
(* Set the directory containing Rubi files *)
SetDirectory["path/to/rubi/directory"];

(* Load Rubi package *)
Get["Rubi.m"]
```

### Method 2: Compiled Package (Faster Loading)

For faster loading, create a compiled MX file:

```mathematica
(* Navigate to Rubi directory *)
SetDirectory["path/to/rubi/directory"];

(* Generate the compiled package *)
Get["MakeRubiMxFile.m"]

(* In future sessions, load the compiled version *)
Get["Rubi.mx"]
```

### Method 3: Step-by-Step Integration Support

To enable step-by-step integration display:

```mathematica
(* Enable ShowSteps before compilation *)
$LoadShowSteps = True;
Get["MakeRubiMxFile.m"]

(* This creates StepRubi.mx instead of Rubi.mx *)
Get["StepRubi.mx"]
```

## 📖 Basic Usage

### Simple Integration

```mathematica
(* Basic integration *)
Int[x^2, x]
(* Returns: x^3/3 *)

Int[Sin[x], x]
(* Returns: -Cos[x] *)

Int[1/(1 + x^2), x]
(* Returns: ArcTan[x] *)
```

### Multiple Integrals

```mathematica
(* Integrate a list of expressions *)
Int[{x^2, Sin[x], 1/(1 + x^2)}, x]
(* Returns: {x^3/3, -Cos[x], ArcTan[x]} *)
```

### Definite Integrals

```mathematica
(* Definite integration (evaluates limits of antiderivative) *)
Int[x^2, {x, 0, 1}]
(* Returns: 1/3 *)
```

### Step-by-Step Integration

```mathematica
(* Show first integration step *)
Int[x*Sin[x], x, Step]

(* Show all integration steps *)
Int[x*Sin[x], x, Steps]

(* Show integration statistics *)
Int[x*Sin[x], x, Stats]
(* Returns: {steps, rules_used, input_complexity, output_complexity, rule_ratio} *)
```

## 🔧 Advanced Features

### Configuration Options

```mathematica
(* Control unintegrable expression handling *)
$Unintegrable = True;  (* Return Unintegrable[expr, var] for non-integrable expressions *)

(* Customize step display colors *)
$RuleColor = Blue;
$ConditionColor = Green;
```

### Utility Functions

Rubi provides numerous utility functions for mathematical analysis:

```mathematica
(* Test mathematical properties *)
FreeQ[expr, x]           (* Test if expression is free of variable x *)
RationalQ[expr]          (* Test if expression is rational *)
TrigQ[expr]              (* Test if expression is trigonometric *)
LogQ[expr]               (* Test if expression is logarithmic *)

(* Simplification utilities *)
Dist[factor, expr, x]    (* Distribute factor over expression *)
Subst[expr, var, value]  (* Substitute value for variable *)
```

## 📚 Documentation

- **[API Reference](docs/API.md)** - Complete function and rule documentation
- **[Rule System Guide](docs/RULES.md)** - Understanding Rubi's integration rules
- **[Examples](docs/EXAMPLES.md)** - Comprehensive usage examples
- **[Developer Guide](docs/DEVELOPMENT.md)** - Contributing and extending Rubi
- **[File Structure](docs/STRUCTURE.md)** - Detailed file organization

## 🎯 Examples

### Algebraic Functions

```mathematica
Int[(a + b*x)^n, x]                    (* Binomial powers *)
Int[x^m*(a + b*x)^n, x]               (* Binomial products *)
Int[x^m*(a + b*x^2)^n, x]             (* Trinomial products *)
Int[Sqrt[a + b*x], x]                 (* Square roots *)
```

### Transcendental Functions

```mathematica
Int[E^x*Sin[x], x]                    (* Exponential-trigonometric products *)
Int[x*Log[x], x]                      (* Logarithmic products *)
Int[Sin[x]*Cos[x], x]                 (* Trigonometric products *)
Int[Sinh[x]*Cosh[x], x]              (* Hyperbolic products *)
```

### Complex Expressions

```mathematica
Int[x^2*E^x*Sin[x], x]               (* Multiple function types *)
Int[x*ArcTan[x], x]                  (* Inverse functions *)
Int[x*Log[1 + x^2], x]               (* Composite functions *)
```

## ⚡ Performance

Rubi is optimized for both accuracy and performance:

- **Rule-based approach** ensures mathematical correctness
- **Compiled MX files** provide fast loading
- **Efficient pattern matching** minimizes computation time
- **Comprehensive rule coverage** reduces failure cases

### Benchmarking

```mathematica
(* Time integration with statistics *)
Timing[result = Int[complex_expression, x, Stats]]

(* Compare with built-in Integrate *)
Timing[Integrate[same_expression, x]]
```

## 🤝 Contributing

Contributions are welcome! Please see our [Developer Guide](docs/DEVELOPMENT.md) for:

- Code style guidelines
- Rule development process
- Testing procedures
- Submission requirements

## 📄 License

This project contains the Rubi integration rules developed by Albert D. Rich. Please refer to the original project documentation for licensing terms.

## 🔗 Links

- **Original Project**: [Applied Mathematics, Western University](http://www.apmaths.uwo.ca/~arich/)
- **Upstream Repository**: [RuleBasedIntegration/Rubi](https://github.com/RuleBasedIntegration/Rubi)
- **Mathematica Documentation**: [Wolfram Language Documentation](https://reference.wolfram.com/language/)

## 📞 Support

For questions and support:

1. **Check the documentation** in the `docs/` directory
2. **Review existing issues** in the repository
3. **Consult the original Rubi documentation**
4. **Create a new issue** with detailed information about your problem

## 🙏 Acknowledgments

- **Albert D. Rich** - Creator and primary developer of Rubi
- **The Wolfram Community** - For ongoing support and feedback
- **Contributors** - For enhancements and bug fixes

---

*Rubi enables sophisticated symbolic integration through its comprehensive rule-based approach, making it an invaluable tool for mathematical computation and education.*