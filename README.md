# BlokDichotomy

A Lean 4 formalization of Blok's dichotomy theorem: the degree of Kripke incompleteness of a
normal modal logic is either $1$ or $2^{\aleph_0}$, with nothing in between. The result is due
to W. J. Blok's 1978 report and is presented in Chagrov and Zakharyaschev's *Modal Logic*,
§10.5. This project depends only on [Mathlib](https://github.com/leanprover-community/mathlib4).

## References

- A. Chagrov, M. Zakharyaschev, *Modal Logic*, Oxford Logic Guides 35, Clarendon Press, 1997.
- W. J. Blok, *On the degree of incompleteness of modal logics and the covering relation in the
  lattice of modal logics*, Report 78-07, Department of Mathematics, University of Amsterdam,
  1978.

## Setup

```bash
lake exe cache get
lake build
lake check
```

## Contributing

See [`AGENTS.md`](AGENTS.md) for the contract this repository holds AI agents to (module
system, citation discipline, the no-`sorry` policy, and where the coding conventions live).
