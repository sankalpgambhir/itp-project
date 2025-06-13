# CS-428 - Constrained Horn Solving for Inductive Propositions

This project features a Coq plugin that establishes a connection between inductively defined propositions and Constrained Horn Clauses (CHCs), developing tactics that leverage established proof search techniques from the CHC literature to automate inductive proofs. It provides an extensible framework that handles both first-order relations and integrates theory reasoning, implementing specialized tactics that prune proof search based on constraint validity.

## Features

- `chc_auto` tactic: Programmatically composes existing Coq tactics through proof tree search
- `hornres` tactic: Explicitly constructs Horn clauses from inductive definitions and performs Prolog-like proof search
- Memoization for improved performance
- Iterative deepening search capabilities
- Integration with theory reasoning (e.g., `lia` for arithmetic constraints)

## Installation

```bash
git clone https://github.com/sankalpgambhir/itp-project.git
cd itp-project
dune build
```

### Available Tactics

First tactic based on the composition of existing Coq tactics for automatic proof search:

- `chc_auto`:
  - Options:
    - `depth=<n>`: Set maximum search depth
    - `deepening`: Use iterative deepening search
    - `no_memo`: Disable memoization
  - Example: `chc_auto with depth=10 deepening.`

Second set of tactics based on explicit extraction and reconstruction:

- `horndfs`: Horn clause proof search using depth-first strategy
- `hornres`: Horn clause proof search using resolution strategy

### Example

Check the `theories/CoLog.v` file for examples of how to use the plugin in Coq. The file contains several inductive definitions and demonstrates the use of the `chc_auto` and `hornres` tactics.

## Project Structure

- `src/`: OCaml implementation of the plugin
  - `ce_api.ml`: Main API functions
  - `ce_syntax.mlg`: Grammar and syntax declarations
  - `prolog.ml`: Prolog-style proof search
  - `resolution.ml`: Resolution-based proof search
  - `term.ml`: Term manipulation utilities

- `theories/`: Coq theories using the plugin
  - `CoLog.v`: Main Coq module with examples

## License

This project is licensed under the Apache 2.0 License.

## Authors

- Sankalp Gambhir
- Auguste Poiroux
