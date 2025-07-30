# Rubi Developer Guide

This guide provides comprehensive information for developers who want to contribute to Rubi, extend its capabilities, or understand its internal architecture. It covers rule development, testing procedures, contribution guidelines, and advanced usage patterns.

## Table of Contents

- [Development Environment Setup](#development-environment-setup)
- [Architecture Overview](#architecture-overview)
- [Rule Development](#rule-development)
- [Testing and Validation](#testing-and-validation)
- [Contributing Guidelines](#contributing-guidelines)
- [Code Style and Standards](#code-style-and-standards)
- [Performance Optimization](#performance-optimization)
- [Advanced Customization](#advanced-customization)
- [Debugging and Troubleshooting](#debugging-and-troubleshooting)

## Development Environment Setup

### Prerequisites

- **Wolfram Mathematica**: Version 10.0 or later
- **Git**: For version control and contributions
- **Text Editor**: With Mathematica syntax highlighting (recommended: VS Code with Wolfram Language extension)

### Setting Up the Development Environment

```mathematica
(* 1. Clone the repository *)
(* git clone <repository-url> *)
(* cd rubi *)

(* 2. Set up development directory *)
SetDirectory["/path/to/rubi/development"];

(* 3. Load Rubi with debugging enabled *)
$DebugMode = True;
$LoadShowSteps = True;
Get["Rubi.m"];

(* 4. Enable additional diagnostic output *)
$ShowPatternMatching = True;
$ShowRuleApplication = True;
```

### Development Tools

```mathematica
(* Utility function for rule testing *)
TestRule[pattern_, result_, conditions_, testCases_] := Module[{},
  Print["Testing rule: ", pattern];
  Do[
    With[{expr = testCase[[1]], var = testCase[[2]]},
      Print["Test: ", expr, " -> ", Int[expr, var]];
      Print["Expected: ", testCase[[3]]];
      Print["Match: ", MatchQ[Int[expr, var], testCase[[3]]]];
    ],
    {testCase, testCases}
  ]
];

(* Rule validation function *)
ValidateRule[rule_] := Module[{pattern, result, conditions},
  (* Extract rule components *)
  {pattern, result, conditions} = ExtractRuleComponents[rule];
  
  (* Validate mathematical correctness *)
  TestMathematicalCorrectness[pattern, result, conditions];
  
  (* Check for conflicts with existing rules *)
  CheckRuleConflicts[pattern, conditions];
  
  (* Performance analysis *)
  AnalyzeRulePerformance[pattern, result];
];
```

## Architecture Overview

### Core Components

1. **Main Package (`Rubi.m`)**
   - Package initialization and setup
   - Rule loading orchestration
   - Global configuration management

2. **Integration Engine**
   - Pattern matching system
   - Rule application logic
   - Recursive integration handling

3. **Rule System**
   - Hierarchical rule organization
   - Condition evaluation system
   - Transformation application

4. **Utility Functions (`Integration Utility Functions.m`)**
   - Mathematical testing predicates
   - Expression manipulation utilities
   - Helper functions for rule conditions

5. **Step Display System (`ShowStep Routines.m`)**
   - Step-by-step integration tracking
   - Rule application visualization
   - Performance statistics collection

### Rule Loading Process

```mathematica
(* Rule loading sequence in Rubi.m *)
LoadRules["Integration utility functions"];           (* Core utilities *)
LoadRules["9.1 Integrand simplification rules"];    (* Preprocessing *)

(* Algebraic function rules *)
LoadRules["1.1.1 Linear binomial products"];
LoadRules["1.1.3 General binomial products"];
(* ... more algebraic rules ... *)

(* Transcendental function rules (conditional) *)
If[Global`$LoadElementaryFunctionRules===True,
  LoadRules["2 Exponentials"];
  LoadRules["3 Logarithms"];
  (* ... more transcendental rules ... *)
];

LoadRules["9.4 Miscellaneous integration rules"];    (* Cleanup rules *)

(* Step display setup (conditional) *)
If[$LoadShowSteps===True, 
  LoadRules["ShowStep routines"];
  StepFunction[Int];
];
```

## Rule Development

### Rule Anatomy

Every Rubi integration rule follows this structure:

```mathematica
Int[pattern_, x_Symbol] :=
  transformation_result /;
condition1 && condition2 && ... && conditionN
```

#### Components Explained

1. **Pattern**: Matches specific types of integrands
2. **Transformation**: The mathematical transformation applied
3. **Conditions**: Constraints that must be satisfied

### Pattern Development Guidelines

#### 1. Pattern Specificity Hierarchy

Place more specific patterns before general ones:

```mathematica
(* Specific case first *)
Int[x_^2*Sin[x_], x_Symbol] :=
  -x^2*Cos[x] + 2*Int[x*Cos[x], x] /;
FreeQ[{}, x]

(* General case after *)
Int[x_^n_*Sin[x_], x_Symbol] :=
  -x^n*Cos[x] + n*Int[x^(n-1)*Cos[x], x] /;
FreeQ[n, x] && IntegerQ[n] && n > 0
```

#### 2. Optional Pattern Usage

Use `_.` for optional patterns with defaults:

```mathematica
(* a and b are optional (default to 1) *)
Int[(a_.+b_.*x_)^m_, x_Symbol] :=
  (a+b*x)^(m+1)/(b*(m+1)) /;
FreeQ[{a,b,m},x] && NeQ[m,-1]
```

#### 3. Pattern Naming Conventions

- `x_Symbol`: Integration variable (always a symbol)
- `a_, b_, c_`: Parameters (typically constants)
- `m_, n_, p_`: Exponents and powers
- `u_, v_, w_`: Subexpressions
- `F_`: Function names (Sin, Cos, etc.)

### Condition Development

#### Essential Condition Types

1. **Variable Independence**: `FreeQ[{a,b,c}, x]`
2. **Type Checking**: `IntegerQ[n]`, `RationalQ[m]`
3. **Mathematical Constraints**: `NeQ[m, -1]`, `GtQ[a, 0]`
4. **Pattern Validation**: `LinearQ[u, x]`, `TrigQ[expr]`

#### Advanced Condition Examples

```mathematica
(* Complex condition for trinomial rules *)
Int[x_^m_*(a_+b_.*x_+c_.*x_^2)^n_, x_Symbol] :=
  result /;
FreeQ[{a,b,c,m,n}, x] &&           (* Parameters free of x *)
NeQ[b^2-4*a*c, 0] &&               (* Non-degenerate quadratic *)
IntegerQ[m] &&                     (* Integer power of x *)
(RationalQ[n] || IntegerQ[n+1/2]) && (* Rational or half-integer n *)
IGtQ[m, 0] &&                      (* Positive integer m *)
(ILtQ[n, 0] || IGtQ[m+2*n+1, 0])   (* Additional constraint *)
```

### Transformation Development

#### Common Transformation Patterns

1. **Direct Integration**
```mathematica
Int[x_^n_, x_Symbol] := x^(n+1)/(n+1) /; FreeQ[n,x] && NeQ[n,-1]
```

2. **Integration by Parts**
```mathematica
Int[x_*Sin[x_], x_Symbol] := -x*Cos[x] + Int[Cos[x], x]
```

3. **Substitution**
```mathematica
Int[(a_.+b_.*u_)^m_, x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m,x], x, u] /;
FreeQ[{a,b,m},x] && LinearQ[u,x] && NeQ[u,x]
```

4. **Reduction Rules**
```mathematica
Int[Sin[x_]^n_, x_Symbol] :=
  -Sin[x]^(n-1)*Cos[x]/n + (n-1)/n*Int[Sin[x]^(n-2), x] /;
FreeQ[n,x] && IGtQ[n, 1]
```

### Example: Developing a New Rule

Let's develop a rule for `∫ x^2 * e^x * sin(x) dx`:

#### Step 1: Identify the Pattern
```mathematica
pattern = x_^2*E^x_*Sin[x_]
```

#### Step 2: Determine the Mathematical Approach
Use repeated integration by parts:
- First: `u = x^2 * sin(x)`, `dv = e^x dx`
- Continue recursively

#### Step 3: Write the Rule
```mathematica
Int[x_^2*E^x_*Sin[x_], x_Symbol] :=
  E^x*(x^2*Sin[x] - 2*x*Cos[x] - 2*Sin[x])/2 + 
  E^x*(x^2*Cos[x] + 2*x*Sin[x] - 2*Cos[x])/2 /;
True  (* No additional conditions needed *)
```

#### Step 4: Simplify and Optimize
```mathematica
Int[x_^2*E^x_*Sin[x_], x_Symbol] :=
  E^x*((x^2 - 2)*Sin[x] - 2*x*Cos[x])/2 /;
True
```

#### Step 5: Add to Appropriate File
Add to `4.1 Sine.m` in the appropriate subsection.

## Testing and Validation

### Rule Testing Framework

```mathematica
(* Basic rule test *)
TestIntegrationRule[pattern_, expected_, conditions_] := Module[
  {result, testPassed},
  
  result = Int[pattern, x];
  testPassed = Simplify[D[result, x] - pattern] == 0;
  
  Print["Pattern: ", pattern];
  Print["Result: ", result];
  Print["Expected: ", expected];
  Print["Derivative test: ", testPassed];
  Print["Conditions satisfied: ", And @@ conditions];
  
  testPassed && And @@ conditions
];

(* Comprehensive test suite *)
RunRuleTests[ruleFile_] := Module[{tests, results},
  tests = ExtractTestsFromFile[ruleFile];
  results = Map[TestIntegrationRule @@ # &, tests];
  
  Print["Total tests: ", Length[tests]];
  Print["Passed: ", Count[results, True]];
  Print["Failed: ", Count[results, False]];
  
  results
];
```

### Validation Procedures

#### 1. Mathematical Correctness
```mathematica
ValidateMathematically[rule_] := Module[{pattern, result},
  {pattern, result} = ExtractPatternAndResult[rule];
  
  (* Check that derivative of result equals original pattern *)
  Simplify[D[result, x] - pattern] == 0
];
```

#### 2. Boundary Case Testing
```mathematica
TestBoundaryCases[rule_] := Module[{},
  (* Test with edge values *)
  TestRule[rule, {x -> 0, x -> 1, x -> -1, x -> Infinity}];
  
  (* Test with symbolic parameters *)
  TestRule[rule, {a -> 0, b -> 1, n -> 0, n -> 1, n -> -1}];
];
```

#### 3. Performance Testing
```mathematica
BenchmarkRule[rule_, testCases_] := Module[{timings},
  timings = Map[
    Timing[Int[#[[1]], #[[2]]]][[1]] &,
    testCases
  ];
  
  {Mean[timings], StandardDeviation[timings], Max[timings]}
];
```

### Regression Testing

```mathematica
(* Automated regression test suite *)
RunRegressionTests[] := Module[{testSuite, results},
  testSuite = {
    (* Polynomial tests *)
    {x^3, x, x^4/4},
    {(1+x)^5, x, (1+x)^6/6},
    
    (* Exponential tests *)
    {E^x, x, E^x},
    {x*E^x, x, E^x*(x-1)},
    
    (* Trigonometric tests *)
    {Sin[x], x, -Cos[x]},
    {x*Sin[x], x, -x*Cos[x] + Sin[x]},
    
    (* Add more test cases... *)
  };
  
  results = Map[
    Function[{test},
      Module[{expr, var, expected, result},
        {expr, var, expected} = test;
        result = Int[expr, var];
        Simplify[D[result, var] - expr] == 0
      ]
    ],
    testSuite
  ];
  
  Print["Regression tests passed: ", Count[results, True], "/", Length[results]];
  results
];
```

## Contributing Guidelines

### Contribution Process

1. **Fork the Repository**
   ```bash
   git fork <upstream-repo>
   git clone <your-fork>
   cd rubi
   ```

2. **Create Feature Branch**
   ```bash
   git checkout -b feature/new-integration-rules
   ```

3. **Develop and Test**
   - Add new rules or functionality
   - Run comprehensive tests
   - Document changes

4. **Submit Pull Request**
   - Provide clear description
   - Include test results
   - Reference related issues

### Code Review Checklist

#### For Rule Contributions
- [ ] Rule pattern is appropriately specific
- [ ] Conditions are mathematically correct
- [ ] Transformation is mathematically valid
- [ ] Rule is placed in correct file and position
- [ ] Comprehensive tests are included
- [ ] Documentation is updated

#### For Code Contributions
- [ ] Code follows established style guidelines
- [ ] Functions are properly documented
- [ ] Error handling is appropriate
- [ ] Performance impact is considered
- [ ] Backward compatibility is maintained

### Submission Requirements

1. **Test Coverage**
   - All new rules must include test cases
   - Minimum 5 test cases per rule
   - Include boundary and edge cases

2. **Documentation**
   - Update relevant documentation files
   - Include usage examples
   - Document any new functions or variables

3. **Performance**
   - Benchmark against existing rules
   - Ensure no significant performance regression
   - Optimize for common use cases

## Code Style and Standards

### Mathematica Coding Standards

#### 1. Naming Conventions
```mathematica
(* Function names: PascalCase *)
IntegrateByParts[u_, dv_, x_] := ...

(* Variable names: camelCase *)
integrationResult = Int[expr, x];

(* Constants: UPPER_CASE *)
$MAXIMUM_RECURSION_DEPTH = 100;

(* Pattern variables: lowercase with underscore *)
Int[x_^n_, var_Symbol] := ...
```

#### 2. Formatting Guidelines
```mathematica
(* Line length: maximum 100 characters *)

(* Function definitions *)
FunctionName[param1_, param2_] := Module[{localVar1, localVar2},
  localVar1 = Computation[param1];
  localVar2 = Computation[param2];
  Return[localVar1 + localVar2]
];

(* Rule definitions *)
Int[pattern_, x_Symbol] :=
  transformation /;
condition1 && 
condition2 && 
condition3
```

#### 3. Documentation Standards
```mathematica
(* Function documentation *)
FunctionName::usage = "FunctionName[param1, param2] computes the integration result using specified parameters.";

(* Rule documentation *)
(* ::Text:: *)
(*This rule handles integration of polynomial-exponential products using integration by parts.*)

Int[x_^n_*E^x_, x_Symbol] :=
  (* Result explanation *)
  x^n*E^x - n*Int[x^(n-1)*E^x, x] /;
FreeQ[n, x] && IntegerQ[n] && n > 0
```

### File Organization Standards

#### 1. File Header Format
```mathematica
(* ::Package:: *)

(* ::Title:: *)
(*File Name and Purpose*)

(* ::Author:: *)
(*Author Name <email@domain.com>*)

(* ::Summary:: *)
(*Brief description of file contents and purpose*)

(* ::Keywords:: *)
(*integration, rules, polynomials, exponentials*)

(* ::Version:: *)
(*1.0 - Initial version*)
(*1.1 - Added advanced polynomial rules*)
```

#### 2. Section Organization
```mathematica
(* ::Section:: *)
(*Main Category*)

(* ::Subsection::Closed:: *)
(*Specific Rule Group*)

(* ::Subsubsection::Closed:: *)
(*Individual Rule Type*)

(* Rule implementation *)
Int[pattern_, x_Symbol] := result /; conditions

(* ::Text:: *)
(*Explanatory text when needed*)
```

## Performance Optimization

### Rule Ordering Optimization

Rules should be ordered from most specific to most general:

```mathematica
(* Most specific: exact pattern match *)
Int[x_^2*Sin[x_], x_Symbol] := (* specific result *) /; True

(* More general: parameterized pattern *)
Int[x_^n_*Sin[x_], x_Symbol] := (* general result *) /; IntegerQ[n] && n > 0

(* Most general: fallback pattern *)
Int[u_*Sin[v_], x_Symbol] := (* generic result *) /; (* complex conditions *)
```

### Condition Optimization

#### 1. Fast Conditions First
```mathematica
(* Good: cheap tests first *)
Int[pattern_, x_Symbol] :=
  result /;
FreeQ[a, x] &&                    (* Fast: simple pattern check *)
IntegerQ[n] &&                    (* Fast: type check *)
IGtQ[n, 0] &&                     (* Fast: simple comparison *)
ComplexCondition[a, b, n]         (* Expensive: last *)

(* Bad: expensive tests first *)
Int[pattern_, x_Symbol] :=
  result /;
ComplexCondition[a, b, n] &&      (* Expensive: first *)
FreeQ[a, x]                       (* Fast: wasted if first fails *)
```

#### 2. Condition Caching
```mathematica
(* Cache expensive condition results *)
CachedConditionQ[expr_] := CachedConditionQ[expr] = 
  ExpensiveConditionTest[expr];
```

### Memory Management

```mathematica
(* Clear intermediate results *)
Module[{temp1, temp2, result},
  temp1 = IntermediateComputation[expr];
  temp2 = AnotherComputation[temp1];
  result = FinalComputation[temp2];
  
  (* temp1 and temp2 are automatically cleared *)
  result
]

(* Use Block for temporary variable assignments *)
Block[{$RecursionLimit = 1000, $IterationLimit = 10000},
  (* Computation with modified limits *)
  Int[complexExpression, x]
]
```

## Advanced Customization

### Custom Rule Sets

```mathematica
(* Define custom rule package *)
BeginPackage["CustomRules`"];

CustomInt::usage = "CustomInt[expr, x] integrates using custom rules.";

Begin["`Private`"];

(* Custom integration rules *)
CustomInt[x_^n_*MyFunction[x_], x_Symbol] :=
  (* Custom transformation *) /;
(* Custom conditions *)

End[];
EndPackage[];

(* Load and use custom rules *)
Get["CustomRules.m"];
CustomInt[x^2*MyFunction[x], x]
```

### Integration Hooks

```mathematica
(* Pre-processing hook *)
$PreIntegrationHook = Function[{expr, var},
  Module[{simplified},
    simplified = Simplify[expr];
    Print["Simplified: ", expr, " -> ", simplified];
    simplified
  ]
];

(* Post-processing hook *)
$PostIntegrationHook = Function[{result, expr, var},
  Module[{verified},
    verified = Simplify[D[result, var] - expr] == 0;
    If[!verified, Print["Warning: Result verification failed"]];
    result
  ]
];

(* Modified Int function with hooks *)
IntWithHooks[expr_, var_] := Module[{preprocessed, result},
  preprocessed = $PreIntegrationHook[expr, var];
  result = Int[preprocessed, var];
  $PostIntegrationHook[result, expr, var]
];
```

### Rule Profiling

```mathematica
(* Profile rule usage *)
$RuleProfiler = <||>;

ProfiledInt[expr_, var_] := Module[{result, startTime, endTime},
  startTime = AbsoluteTime[];
  result = Int[expr, var];
  endTime = AbsoluteTime[];
  
  (* Record timing information *)
  AppendTo[$RuleProfiler, 
    expr -> <|"time" -> endTime - startTime, "result" -> result|>];
  
  result
];

(* Analyze profiling results *)
AnalyzeRuleProfile[] := Module[{timings, slowest},
  timings = Values[$RuleProfiler][[All, "time"]];
  slowest = TakeLargest[$RuleProfiler, 10, #["time"] &];
  
  Print["Average time: ", Mean[timings]];
  Print["Slowest integrations: ", slowest];
];
```

## Debugging and Troubleshooting

### Debug Mode Setup

```mathematica
(* Enable comprehensive debugging *)
$DebugMode = True;
$ShowSteps = True;
$ShowRuleMatching = True;
$ShowConditionEvaluation = True;

(* Debug-enabled Int function *)
DebugInt[expr_, var_] := Module[{result, trace},
  If[$DebugMode,
    Print["Integrating: ", expr, " with respect to ", var];
    Print["Pattern matching phase..."];
  ];
  
  trace = Trace[Int[expr, var], _Int, TraceInternal -> True];
  result = Int[expr, var];
  
  If[$DebugMode,
    Print["Integration trace: ", trace];
    Print["Final result: ", result];
  ];
  
  result
];
```

### Common Issues and Solutions

#### 1. Rule Conflicts
```mathematica
(* Detect rule conflicts *)
DetectRuleConflicts[pattern1_, pattern2_] := Module[{overlap},
  overlap = FindPatternOverlap[pattern1, pattern2];
  If[overlap =!= {},
    Print["Warning: Pattern overlap detected"];
    Print["Patterns: ", pattern1, " and ", pattern2];
    Print["Overlap: ", overlap];
  ];
];
```

#### 2. Infinite Recursion
```mathematica
(* Recursion depth monitoring *)
$RecursionDepth = 0;
$MaxRecursionDepth = 50;

SafeInt[expr_, var_] := Module[{result},
  $RecursionDepth++;
  
  If[$RecursionDepth > $MaxRecursionDepth,
    $RecursionDepth--;
    Return[CannotIntegrate[expr, var]];
  ];
  
  result = Int[expr, var];
  $RecursionDepth--;
  result
];
```

#### 3. Performance Issues
```mathematica
(* Performance monitoring *)
MonitorPerformance[expr_, var_] := Module[{timing, memory, result},
  {timing, {memory, result}} = 
    Timing[MaxMemoryUsed[Int[expr, var]]];
  
  If[timing > 5.0,
    Print["Warning: Slow integration (", timing, " seconds)"];
  ];
  
  If[memory > 100*1024*1024,
    Print["Warning: High memory usage (", memory/1024/1024, " MB)"];
  ];
  
  result
];
```

### Testing Framework

```mathematica
(* Comprehensive test runner *)
RunDeveloperTests[] := Module[{tests, results},
  Print["Running developer test suite..."];
  
  tests = {
    TestRuleCorrectness[],
    TestPerformanceRegression[],
    TestRuleConflicts[],
    TestBoundaryConditions[],
    TestMemoryUsage[]
  };
  
  results = Map[Function[test, 
    Print["Running: ", test];
    TimeConstrained[test, 300, $Failed]
  ], tests];
  
  Print["Test results: ", results];
  And @@ (results =!= $Failed)
];
```

---

*This developer guide provides the foundation for contributing to and extending Rubi. For specific implementation details, consult the source code and the [API Reference](API.md).*