# Working in BlokDichotomy

BlokDichotomy formalizes Blok's dichotomy theorem: the degree of Kripke incompleteness of a
normal modal logic is either $1$ or $2^{\aleph_0}$, never anything in between. The result is
reported in Chagrov and Zakharyaschev, *Modal Logic* (CZ98), §10.5, attributing it to Blok's 1978
report. The formalization roadmap and the Japanese proof notes are kept locally under
`.claude/proofs/` (git-ignored, not part of the repository); read them, when present, before
planning a new step.

This file is the contract for AI agents working in this repository.

## Setup

Proof work uses the `lean4` plugin (marketplace `lean4-skills`, providing `/lean4:autoprove` etc.)
and the `lean-lsp` MCP server (defined in `.mcp.json`; requires `uv` and `ripgrep`):

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```

This file is the only instruction file here; no `CLAUDE.md` is checked in. Claude Code reads
`AGENTS.md` through its built-in `agents-md` plugin, whose default mode steps in only for a project
with no instruction file of its own — a `CLAUDE.md`, `.claude/CLAUDE.md` or `CLAUDE.local.md`
anywhere from the filesystem root down to the working directory makes it stand down and leaves this
file unread. Per-clone notes therefore belong in `.claude/AGENTS.md`, which is git-ignored and read
beside this file.

## GitHub

This is a single-maintainer repository, so the process is lighter than a team project's.

- **Claim an issue before working on it**: `gh issue edit <n> --add-assignee @me`.
- **One branch, one pull request.** Branch from `main`; never push directly to `main`.
- **Don't merge without being told to.** Open the PR and wait; merge only once told to for that
  PR.

## The rules of the code

- Every file opts into the Lean module system: it starts with `module`, imports are
  `public import`, and the module docstring precedes `@[expose] public section`.
- `lake build BlokDichotomy --wfail` must be green — no errors, no warnings.
- **Never write `sorry` or `axiom`.** A proof that is not finished stays out of the pull request.
  `lake check` rejects both: it checks that `BlokDichotomy.Main` proves the statement in `Challenge.lean` with only the standard axioms.
- **Follow Foundation's contribution guidelines**, copied verbatim into this repository as
  [`docs/index.md`](docs/index.md), [`docs/style.md`](docs/style.md), and
  [`docs/refactoring.md`](docs/refactoring.md). [`docs/conventions.md`](docs/conventions.md)
  lists what this repository adds or changes.
- **Cite the source.** Every non-trivial definition and theorem carries, at the end of its
  docstring, the reference it formalizes, one line per key: `- [CZ98, Theorem 10.55]`,
  `- [Blok78, Lemma 4.4]`. The keys are looked up in [`references.yml`](references.yml). If none
  exists, omit the docstring unless a concise statement-level explanation is useful.
- **Generic material goes to its own module, sorted by where it is headed.** A lemma that
  mentions none of the notions particular to this project — a Mathlib gap, a general
  order-theoretic or set-theoretic fact — does not belong next to the theorem that first needed
  it; it goes to `BlokDichotomy/ToMathlib/`, sorted as if destined for Mathlib itself.
- **No compatibility layer.** When you rename, move, or delete a declaration, update every use in
  the same PR and remove the old name. No aliases, wrappers, forwarding modules, or deprecation
  shims.
- **No development artifacts** in the code: plan steps, issue numbers, "TODO after review",
  skeleton-era comments.

## Dependencies

This project depends on **Mathlib only**; it does not depend on
[Foundation](https://github.com/FormalizedFormalLogic/Foundation). Modal logic formalizations
elsewhere — notably
[ModalLogic](https://github.com/FormalizedFormalLogic/ModalLogic) (in particular its
`ModalLogicArchive`) and
[ProvabilityLogic](https://github.com/FormalizedFormalLogic/ProvabilityLogic) — are useful as
reference implementations to read for vocabulary and proof strategy, but nothing here imports
from them; definitions needed here are restated against Mathlib directly.

## Language

Code, docstrings, commit messages, and pull request bodies are written in English. The local proof
notes under `.claude/proofs/` are written in Japanese, following the `japanese-tech-writing`
skill's norms; they are a per-clone working aid, so there is no build recipe for them in the
repository.

## Sources

The reference texts are kept locally under `.claude/references/` (CZ98's chapters and Blok's
1978 report). They are copyrighted and git-ignored: read them and cite them, never commit them
or paste long passages from them.
