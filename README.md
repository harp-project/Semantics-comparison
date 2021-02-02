# Semantics-comparison

This project aims to investigate and compare different big-step style formal semantics and their usability, executability. We use a small Core Erlang-like functional language for this purpose. The structure of the files is the following:

- `CE_Syntax.v` contains the syntax and semantic domain for the language
- `CE_Helpers.v` contains helper functions and lemmas about the syntax
- `CE_Env.v` contains the definition of environments and the correcponding functions
- `CE_Aux.v` contains the definition of auxiliary functions which are used when evaluating `ECall` expressions
- `CE_NOS.v` contains the traditional inductive big-step semantics
- `CE_PBOS.v` contains the pretty-big-step semantics
- `CE_FBOS.v` contains the functional big-step semantics
- `CE_Tests.v` contains simple expression evaluation tests
- `CE_Equivs.v` contains expression equivalence proofs, moreover, theorems about the functional big-step semantics, and semantics equivalence

The source code is licensed under GPL v3.

# Acknowledgements

Supported by the project "Integrált kutatói utánpótlás-képzési program az informatika és számítástudomány diszciplináris területein (Integrated program for training new generation of researchers in the disciplinary fields of computer science)", No. EFOP-3.6.3-VEKOP-16-2017-00002. The project has been supported by the European Union and co-funded by the European Social Fund.
