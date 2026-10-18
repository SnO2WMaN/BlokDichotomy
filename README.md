# BlokDichotomy

A Lean 4 formalization of Blok's dichotomy theorem.
This project depends only on [Mathlib](https://github.com/leanprover-community/mathlib4).

## References

- A. Chagrov, M. Zakharyaschev, *Modal Logic*, Oxford Logic Guides 35, Clarendon Press, 1997.
- W. J. Blok, *On the degree of incompleteness of modal logics and the covering relation in the
  lattice of modal logics*, Report 78-07, Department of Mathematics, University of Amsterdam,
  1978.

## Import graph

![Import graph](https://sno2wman.github.io/BlokDichotomy/import-graph.png)

## Setup

```bash
lake exe cache get
lake build
lake check
```

## Contributing

See [`AGENTS.md`](AGENTS.md) for the contract this repository holds AI agents to (module
system, citation discipline, the no-`sorry` policy, and where the coding conventions live).
