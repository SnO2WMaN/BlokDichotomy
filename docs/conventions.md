# Coding conventions

BlokDichotomy follows **Foundation's contribution guidelines**: [`index.md`](index.md),
[`style.md`](style.md), and [`refactoring.md`](refactoring.md) in this directory are copied from
the `contribute/` directory of
[Foundation](https://github.com/FormalizedFormalLogic/Foundation/tree/master/contribute), under
its Apache-2.0 license, with one substitution: every `just forgive` is dropped,
this repository checks with `lake check` instead.

Those documents are the authority; BlokDichotomy follows them as written, except where this file
records a difference or addition below — in which case this file wins. Where they say
"Foundation", read "Foundation, and BlokDichotomy"; where they name Foundation-specific files
(`Foundation.lean`, `references.bib`, `just` recipes), the counterparts here are the ones named
below. BlokDichotomy does not re-copy these files automatically on any schedule, since it tracks
no Foundation pin; re-copy by hand if Foundation's guidelines change in a way worth adopting.

The reason for following Foundation's conventions at all, despite depending only on Mathlib, is
practical: the house style (proof shape, naming, citation discipline, no `sorry`) is
well-tested, and reusing it means one less thing to design from scratch.

## BlokDichotomy-specific additions

- **Module system.** Every file opts into the Lean module system exactly as Foundation does: it
  starts with `module`, imports are `public import`, and the module docstring precedes
  `@[expose] public section`.
- **Root module.** `BlokDichotomy.lean` imports every module and is regenerated with
  `just mk-all` (`lake exe mk_all --lib BlokDichotomy --module`); CI checks it.
- **Linters.** The library builds with Mathlib's standard linter set, which `lakefile.toml`
  opts into wholesale (`weak.linter.mathlibStandardSet`), minus the header linter; `autoImplicit`
  is off, as in Mathlib. A warning is an error: CI and the pre-push hook build with
  `lake build BlokDichotomy --wfail`. Fix a warning, never suppress it.
- **Focus dots are `·`, not `.`, overriding `style.md`'s house preference.** `style.md` calls the
  ASCII `.` bullet the house style; that clashes with Mathlib's `linter.style.cdot`, which this
  repository's linter set enables and which rejects `.` in favor of `·` (typed as `\.`). The
  linter wins, since `--wfail` makes it a build failure either way: write `·`.
- **Universe variables must be declared.** With `autoImplicit` off, a bare `u`, `v`, `w` used as
  a universe level in a signature is not auto-bound; declare it first with `universe u v` (see
  any file under `BlokDichotomy/` for the pattern). The same goes for an ordinary free variable
  used only in a `lemma`/`theorem` signature: bind it explicitly, either inline or via a
  preceding `variable`.
- **Citations.** The bibliography is [`references.yml`](../references.yml) at the repository
  root, written in [Hayagriva](https://github.com/typst/hayagriva) YAML rather than
  Foundation's BibTeX `references.bib`; there is no `bibtool` step, the file is edited by hand
  and kept sorted by key. Its keys are the citation keys (`CZ98`, `Blok78`), cited at the end of
  the docstring in Foundation's form, one line per key:
  ```
  - [CZ98, Theorem 10.55]
  - [Blok78, Lemma 4.4]
  ```
  A key used in a docstring must have an entry in `references.yml`; add the entry in the same
  pull request.
- **No `sorry`, no `axiom`.** Unfinished proofs stay out of the pull request; `lake check` rejects both.
- **Reuse before restating.** This project depends only on Mathlib — see
  [`AGENTS.md`](../AGENTS.md#dependencies) for why it does not depend on Foundation. Mathlib's
  vocabulary (orders, lattices, cardinality, `SetLike`, …) is what a new definition should build
  on; search it before defining anything. Modal-logic-specific definitions (formulas, Kripke
  frames, normal logics) have no Mathlib counterpart and are defined here from scratch, informed
  by — but not copied wholesale from — [ModalLogic](https://github.com/FormalizedFormalLogic/ModalLogic)
  and [ProvabilityLogic](https://github.com/FormalizedFormalLogic/ProvabilityLogic).
- **`<|` for low-precedence application.** Write `f <| x`, not `f $ x`, and prefer it to
  parentheses whenever the argument runs to the end of the term: `exact Or.inr <| Or.inl h`, not
  `exact Or.inr (Or.inl h)`. Foundation's guidelines do not choose between the two spellings;
  Mathlib's `style.dollarSyntax` linter does, and this repository follows it.
- **Names after two or more people use their lowercase initials.** A declaration named after a
  result or construction credited to two or more people starts with the lowercase initials of
  their surnames, followed by the rest of the name in camel case: the Blok–Esakia isomorphism is
  `beIsomorphism`, not `blokEsakia` or `blokEsakiaIsomorphism`. A name after a single person
  keeps the surname. Names that predate this rule (the Jankov–Fine ones) are left as they are.
- **Upward closed, not upset.** Say "upward closed set" and "downward closed set", not "upset" and
  "downset", in docstrings and in names: `Frame.IsUpwardClosed`, `isUpwardClosed_boxSet`.
- **Avoid `?_`.** Prefer `apply f` to `refine f ?_`, and a direct term to a `refine` with holes;
  [`style.md`](style.md)'s preference for direct term construction is the same rule seen from the
  other side.
- **AI disclosure.** As in Foundation: every commit carries a `Co-Authored-By` trailer for the
  model, and the PR body says an AI agent wrote it.

## Checks before opening a pull request

```bash
lake build BlokDichotomy --wfail   # no errors and no warnings
lake check                         # kernel replay; only standard axioms
just mk-all                        # BlokDichotomy.lean up to date
```

