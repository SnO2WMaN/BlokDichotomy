# List available recipes
default:
    @just --list

# Build the library (Mathlib comes from the cache)
build:
    lake exe cache get
    lake build

# Regenerate BlokDichotomy.lean to import all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --lib BlokDichotomy --module

# Regenerate the import graph of the library (needs graphviz; output is git-ignored, in `import-graph/`)
import-graph:
    mkdir -p import-graph
    lake exe graph --to BlokDichotomy --mark-sorry \
      import-graph/import-graph.dot \
      import-graph/import-graph.png \
      import-graph/import-graph.svg

# Install the git hooks that run the CI checks before a push (needs lefthook: https://lefthook.dev)
hooks:
    lefthook install
