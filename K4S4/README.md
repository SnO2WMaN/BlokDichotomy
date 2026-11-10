# Kripke incompleteness in NExt K4 and NExt S4

We investigate the degree of Kripke incompleteness among normal extensions of `K4`
and of `S4` together. Our first focus is on logics with continuum many frame
companions in these lattices. The workspace remains under `K4S4/`.
Proof ideas and strategy are developed in discussion; implementation proceeds one
agreed step at a time.

## Working method

We work primarily in Markdown files, writing and discussing ordinary mathematical
proofs. Each substantive proof step should be recorded in a `.md` file with its
statement, assumptions, argument, and any unresolved gaps or questions. This README
is the entry point; focused proof files can be added as the discussion develops.

Lean experiments are optional, and not every argument needs formal verification.
When Lean code is written, it must be accompanied by a self-contained mathematical
account in Markdown, so the user can follow and assess the proof without reading
the code. Once we have worked out a good proof, we can formalize it. Clearly label
conjectures, informal proofs, unchecked Lean, and Lean-checked results.

## Conventions

For `L : Modal.NormalLogic ℕ` extending the respective base logic, we study

```lean
L.degree.{0} 𝐊𝟒 (fun _ _ => True)
L.degree.{0} 𝐒𝟒 (fun _ _ => True)
```

These count normal extensions of `K4` or `S4` having the same validating Kripke
frames as `L`. The base logic restricts the companions being counted; the frame
predicate above includes all frames in `Type`. These degrees differ from counting
companions among all normal extensions of `K`.

For a logic `L` extending `S4`,

\[
1 \leq \deg_{\mathrm{NExt}\,S4}(L)
  \leq \deg_{\mathrm{NExt}\,K4}(L) \leq 2^{\aleph_0}.
\]

Every `S4` companion is also a `K4` companion, and the existing general cardinal
bound supplies the last inequality. Consequently, continuum degree in `NExt S4`
implies continuum degree in `NExt K4`. This implication is Lean-checked in
`Experiments.lean`, using `degree_le_degree_of_isNExt` and `degree_le_continuum`.

## Literature

Put useful papers, books, and notes in [`literature/`](literature/README.md).
The user and agent may both add sources; internet searches and downloads of relevant,
accessible material are permitted. If a needed source is inaccessible, the agent
can ask the user for it. Record source details and relevant pages or results in
the folder's `README.md`. Source files are git-ignored by default.

## Experimental environment

This folder shares the repository's Lean toolchain, Mathlib dependency, and existing
formalization. No separate Lake project or dependency installation is needed.

Run from the repository root:

```bash
lake build K4S4 --wfail
lake env lean K4S4/Experiments.lean
```

[`ContinuumManyDegreeContinuum.lean`](ContinuumManyDegreeContinuum.lean) proves
the existence and exact cardinality of Kripke-complete S4 extensions of continuum
degree in `NExt S4`. Its concrete frame construction and naming lemmas are in
[`Construction/`](Construction/). The optional `K4S4` target builds these modules
as well as the experiments.

`Experiments.lean` contains small examples applying existing results: the degree
bounds, the continuum-degree implication from `NExt S4` to `NExt K4`, and validity
of the `4` scheme on transitive frames.

The `K4S4` target is optional. The default target and `BlokDichotomy.lean` continue to
build the established formalization. Check it with:

```bash
lake build BlokDichotomy --wfail
```

## Mathematical notes

[Continuum many Kripke-complete S4 extensions of continuum degree](ContinuumManyDegreeContinuum.md)
is a Lean-checked proof using the general frames described in
[The indexed S4 construction](Construction.md). Splitting its indices into even and odd numbers gives
continuum many different Kripke-complete logics, each with continuum many
companions in `NExt S4`. The odd indices distinguish their validating frame
classes, and the even indices distinguish the companions within each class.
Both the general-frame construction and this application are formalized in Lean.
