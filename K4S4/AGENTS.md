# Working on K4 and S4

This subproject investigates the degree of Kripke incompleteness in `NExt K4` and
`NExt S4` together, starting with logics whose degree in these lattices is the continuum.
The workspace remains under `K4S4/`. The repository's
[`AGENTS.md`](../AGENTS.md) and coding conventions also apply here.

## Collaboration

- Work interactively with the user. Discuss the mathematical idea and proof strategy
  before substantial implementation, then implement the agreed next step.
- Keep each step small enough to review and discuss. Do not start a comprehensive
  formalization or commit to a full project roadmap without a request.
- Markdown files are the primary medium for mathematical collaboration. For every
  substantive proof step, create or update a `.md` file under `K4S4/` with the statement,
  assumptions, argument, and any gaps or questions that need discussion.
- Write ordinary mathematical proofs in Markdown first. Develop and discuss a good
  proof before formalizing it in Lean; a Lean implementation is not required for each
  research step, and not every argument needs Lean verification.
- When Lean code is produced, also provide a self-contained mathematical account in
  Markdown. The user will not always read the Lean files and must be able to assess
  the argument from the Markdown alone.
- Informal arguments, counterexamples, and selective Lean experiments are all useful
  outcomes. Follow the user's choice of whether a step needs Lean verification.
- Distinguish conjectures, informal proofs, unchecked Lean, and Lean-checked results.
  Report exactly what was checked; never describe an informal argument as formalized.

## Workspace

- Keep this investigation under `K4S4/`. Use `README.md` as the entry point to shared
  mathematical notes, add focused `.md` proof files as needed, and use
  `Experiments.lean` for selective Lean experiments.
- Read relevant material in `literature/` and local notes under `../.claude/proofs/`,
  when present, before proposing a new proof step.
- Use the parent Lake project and its pinned Lean and Mathlib versions. The optional
  `K4S4` library is built with `lake build K4S4 --wfail` from the repository root.
- Keep experimental modules out of `BlokDichotomy.lean`. Changes to the established
  library should serve an agreed proof step, not anticipate future needs.
- Preserve the repository's prohibition on `sorry` and `axiom`. Keep unfinished
  arguments and proposed statements in Markdown instead of adding proof placeholders.
  Cite literature-backed results according to the parent conventions.

## Literature

- The user supplies useful papers, books, and notes in `K4S4/literature/`. Consult this
  folder as a research source, alongside existing local references.
- Internet searches and downloads of relevant, accessible sources into this folder
  are authorized when useful. Record bibliographic details, source URLs, and relevant
  pages or results in its `README.md`; cite sources in proofs and research notes.
- If a useful source is inaccessible, ask the user for a copy or the relevant excerpt.
- Source files in `literature/` are git-ignored by default. Do not commit copyrighted
  material or reproduce long passages. Add bibliography keys to `../references.yml`
  when citing a source in Lean docstrings.

## Mathematical conventions

- Reuse `Modal.logicK4`, `Modal.logicS4`, `Modal.NExt`, `Modal.NormalLogic.IsNExt`,
  `FrameEquiv`, `Companion`, and `degree` before introducing new definitions.
- Unless explicitly agreed otherwise, use formulas over `ℕ`, frames in `Type`, and
  `L.degree.{0} 𝐊𝟒 (fun _ _ => True)` or `L.degree.{0} 𝐒𝟒 (fun _ _ => True)` for
  the degree in the respective lattice. These count companions extending the chosen
  base logic, with equivalence tested on all Kripke frames.
- For a logic extending `S4`, its degree in `NExt S4` is at most its degree in
  `NExt K4`, which is at most the continuum. Thus continuum degree in `NExt S4`
  implies continuum degree in `NExt K4`. Reuse `degree_le_degree_of_isNExt` and
  `degree_le_continuum` for this implication.
- State explicitly when changing the ambient lattice or frame class. The ordinary
  degree in `NExt K` and the degrees in `NExt K4` and `NExt S4` count different
  companion classes; an ordinary continuum-degree result alone does not establish
  continuum degree in either smaller lattice.
- Treat dichotomy claims in `NExt K4` and `NExt S4` as subjects of investigation.
  Reuse established components without assuming the desired results.
