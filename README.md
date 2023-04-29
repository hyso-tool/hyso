# HySO - Model Checking of Second-Order Hyperproperties

This repository contains HySO - a partial model checker for (a fragment of) Second-Order HyperLTL on finite-state systems.
It is based on the theory presented in 

> Beutner, Finkbeiner, Frenkel, Metzger. Second-Order Hyperproperties. CAV 2023

To clone this repository and initialize submodules run 

```shell
git clone https://github.com/hyso-tool/hyso
cd hyso
git submodule init
git submodule update
```

## Structure 

- `src/` contains the source code of HySO
- `app/` is the target folder for the build. The final HySO executable will be placed here.
- `benchmarks/` contains various benchmarks.


## Build

To build HySO you require the following dependencies:

- [.NET 7 SDK](https://dotnet.microsoft.com/en-us/download) (tested with version 7.0.203)
- [spot](https://spot.lrde.epita.fr/) (tested with version 2.11.5)

Install the .NET 7 SDK (see [here](https://dotnet.microsoft.com/en-us/download) for details).
Download and build spot (details can be found [here](https://spot.lrde.epita.fr/)). 
You can place the spot executables in any location of your choosing. 
HySO requires the *absolute* path to some of the spot executables (see details below).

To build HySO run the following (when in the main directory of this repository).

```shell
cd src/HySO
dotnet build -c "release" -o ../../app
cd ../..
```

Afterward, the `HySO` executable is located in the `app/` folder.

### Connect Spot to HySO

HySO requires the *autfilt* and *ltl2tgba* tools from the [spot library](https://spot.lrde.epita.fr/).
HySO is designed such that it only needs the **absolute** path to these executables, so they can be installed and placed at any location.
The absolute paths are specified in a `paths.json` configuration file. 
This file must be located in the *same* directory as the HySO executables (this convention makes it easy to find the config file, independent of the relative path HySO is called from). 
We already provide a template file `app/paths.json` that **needs to be modified**. 
After having built spot, paste the absolute path to the *autfilt* and *ltl2tgba* executables to the `paths.json` file. 
For example, if `/usr/bin/autfilt` and `/usr/bin/ltl2tgba` are the *autfilt* and *ltl2tgba* executables, respectively, the content of `app/paths.json` should be

```json
{
    "autfilt": "/usr/bin/autfilt",
    "ltl2tgba": "/usr/bin/ltl2tgba"
}
```

### Run HySO

After you have modified the configuration file you can use HySO by running the following
 
```shell
./app/HySO -i <systemPath> <propertyPath>
```
where `<systemPath>` is the (path to the) input system and `<propertyPath>` is the path to the property file.

To check that everything has been set up correctly run 
```shell
./app/HySO -i ./benchmarks/muddy/muddy_system_2.txt ./benchmarks/muddy/muddy_property_2_1.txt
```
which should output `UNSAT`.

# Input to HySO

In this section, we first discuss the command-line options of HySO, followed by the structure of the supported input. 

## Command-line Arguments

You can call HySO by running

```
./app/HySO -i <systemPath> <propertyPath>
```
where `<systemPath>` is a path to a file that contains the input system and `<propertyPath>` is a path to a file that contains the Hyper2LTL property.

For details on how the system and property are specified, we refer to the following sections.   

Additional (optional) command-line options include

- `--debug` prints additional debug outputs

## Specifying Explicit-state Transition Systems

HySO expects an explicit-state transition system of the form

```
aps "<AP>" ... "<AP>"
init <stateID> ... <stateID> 
--BODY-- 
<stateDefinition>
...
<stateDefinition>
```

Here, `<AP>` is an atomic proposition. This can be any string not containing `"`. Note that all atomic propositions are escaped.
`<stateID>` is any natural number specifying a state. 
The header specifies which states are initial (there must be at least one initial state) and which APs are used in the system.

A `<stateDefinition>` has the form 
```
State: <stateID> <apEval>
<stateID> ... <stateID>
```

It specifies which state we are defining and the evaluation of the atomic propositions in that state. 
The `<apEval>` has the form `[(t|f) ... (t|f)]` and specifies if each atomic proposition holds (`t`) or does not hold (`f`). The length of this list must match the number of atomic propositions listed in the header. 
The second line lists all successors of that state.
Every state must have at least one successor state.

Consider the following example:

```
aps "x" "y"
init 0 1
--BODY-- 
State: 0 [f f]
0 2 3
State: 1 [f t]
0 1 2
State: 2 [t f]
0 2 3
State: 3 [t t]
2 3
```

This specification declares states `0` and  `1` as initial states and `"x"` and `"y"` as APs.
For each state, we give the evaluation of the atomic propositions as a list of booleans (either `f`, or `t`).
For example, in state `1`, AP `"x"` does not hold but `"y"` does.
Each state lists all successors of that node. 
For example, the successor states of state `0` are states `0`, `2`, and `3`.



## Specifying Second-Order HyperLTL Properties

The specifications checked by HySO are written in a fragment of Hyper2LTL [1].
A Hyper2LTL formula consists of an LTL-like body, preceded by a quantifier prefix. 
In the prefix both first-order and second-order quantification is possible. 
First-order quantification can either range over the traces in the provided system, an arbitrary trace, or a trace within a second-order variable.
Each second-order variable is defined by a fixpoint operation. 

Formally, a Hyper2LTL formula has the form `<prefix> <body>`.

Here `<body>` can be one of the following:
- `1`: specifies the boolean constant true
- `0`: specifies the boolean constant false
- `"<AP>"_<TVAR>` where `<AP>` is an atomic proposition (any sequence of letters that does not contain `"`) and `<TVAR>` is a trace variable which is any string consisting of letters, digits, and `-` (starting with a letter). This atomic formula holds if the atomic proposition `<AP>` holds in the current step on trace `<TVAR>`. Note that atomic proposition name is escaped in `"`s.
- `(<body>)`: Parenthesis
- `<body> & <body>`: Conjunction
- `<body> | <body>`: Disjunction
- `<body> -> <body>`: Implication
- `<body> <-> <body>`: Equivalence
- `<body> U <body>`: Until
- `<body> W <body>`: Weak Until
- `<body> R <body>`: Release
- `F <body>`: Eventually
- `G <body>`: Globally
- `X <body>`: Next
- `! <body>`: Negation

The operators follow the usual operator precedences. To avoid ambiguity, we recommend always placing parenthesis around each construct. 

The quantifier prefix `<prefix>` can be one of the following:

- The empty string

- Universal or existential trace quantification `forall <TVAR> : <SOVar>. <prefix>` and `exists <TVAR> : <SOVar>. <prefix>`. 
Here `<SOVar>` is a second-order variable which is any string consisting of letters, digits, and `-` (starting with a letter).
There are two special variables: `sys0` refers to the set of traces of the system, and `all` refers to the set of all traces.

- Second-order fixpoint quantification of the form 
```
mu <SOVAR> : iter ([(<TVAR> : <SOVAR>)^*], <init>, <TVAR>, [(<TVAR> : <SOVAR>)^*], <step>, <TVAR>)
```
where `<init>` and `<step>` are quantifier-free formulas (in the `<body>` category).
This quantification defines a <SOVAR> variable as a fixpoint where we define the initial and step condition. 
We give an example below. 


An example property is the following: 

```
mu X : iter([A : sys0],
("a"_A) & (X G("d"_A)),
A, 
[A : X, B : sys0],
(G (("a"_A <-> "a"_B) & ("d"_A <-> "d"_B)))
| 
(G (("c"_A <-> "c"_B) & ("d"_A <-> "d"_B))) 
,
B ).
forall A : X. "a"_A
```

This property defines a second-order variable `X` as follows: 
For the initial condition, we take some trace `A` from the traces of the system. If this trace satisfies `("a"_A) & (X G("d"_A))` then we take the `A` trace and add it to our initial model (given by the trace variable `A` appearing as the third argument).
In the step condition, we define which traces we want to add to the set of traces. 
Here we take any trace `A` in the set `X` we are just defining and any trace `B` in the system. If those two traces satisfy `(G (("a"_A <-> "a"_B) & ("d"_A <-> "d"_B))) | (G (("c"_A <-> "c"_B) & ("d"_A <-> "d"_B)))` then we add trace `B` to the system (indicated by the last argument of `mu`). 
This defines a unique set of traces bound to `X`. 
Afterwards we state that all traces `A` in `X` satisfy the AP `a` in the first step (`forall A : X. "a"_A`). 


## References

[1] Beutner, Finkbeiner, Frenkel, Metzger. Second-Order Hyperproperties. CAV 2023