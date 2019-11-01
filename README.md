# solidity-cfg-builder
A control-flow graph builder for Solidity smart contracts.

## Overview

This package generates a control-flow graph from Solidity contracts. Control-flow graphs are helpful as a graphic representation of the semantics of programs, and are the basis of many static analysis approaches to optimizing and verifying programs. This package is the basis of a static analysis approach I am currently developing. 

solidity-cfg-builder is developed in Haskell, utilising a Solidity syntax parser used in the runtime verification tool for Solidity [contractLarva](https://github.com/gordonpace/contractLarva). The version of the parser used in the project is packaged in the project. 

This tool given Solidity code generates a control-flow graph in DOT notation, which can be visualised using [GraphViz](https://www.graphviz.org/).

## Building the tool

Requirements: [GHC](https://www.haskell.org/ghc/) (e.g. install the full [Haskell Platform](https://www.haskell.org/platform/))

Compilation: Run the following command in the src folder:

> ghc -o solidity-cfg-builder Main.hs

## Tool usage:

For correct results always make sure that the Solidity code compiles with a Solidity compiler.

To use the tool pass the location of a solidity file and the preferred location of the output to the executable, e.g. execute:

> "./solidity-cfg-builder" &lt;solidity-code.sol&gt; &lt;cfg.gv&gt;

## License
This project is licensed under the terms of the [Apache 2.0 license](LICENSE).

## TODO (See Issues for an up-to-date list)
1. <s>Handle function modifiers</s>
2. Allow option to flatten CFGs with function calls (consider also contract inheritance)
3. Handle block of statements at end of function definition
4. Event triggering is being parsed as a function call. Post-process to show triggerring of event explicitly.
----
# FAQ and Common Problems

### When compiling the code I get the error: Could not find module ‘Text.Parsec’.
Make sure you have installed parsec.  Also, see this stackoverflow thread (https://stackoverflow.com/questions/9058914/cant-find-parsec-modules-in-ghci)
>cabal install parsec


