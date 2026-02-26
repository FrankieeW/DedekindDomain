# AGENTS.md — DedekindDomain

This file provides guidance for AI agents operating in this Lean 4 theorem proving project.

## Project Overview

**Project Type**: Lean 4 mathematical theorem proving library
**Lean Version**: v4.29.0-rc2
**Main Dependency**: mathlib (leanprover-community v4.29.0-rc2)
**Source Location**: `DedekindDomain/*.lean`

## Build, Lint, and Test Commands

### Running the Project

```bash
lake exe cache get  # fetches dependencies (mathlib)
# Build the project (compiles all Lean files)
lake build

# Clean build artifacts
lake clean

# Run a single Lean file (useful for quick checks)
lean path/to/file.lean
```

### Running Tests

Lean 4 doesn't have traditional "tests" — proofs are verified during compilation.

```bash
# Build all - verifies all proofs
lake build

# Verify a specific file (fast, uses cached oleans)
lean --ccache DedekindDomain/IntegerRing.lean

# Run a single file without cache (full rebuild)
lean DedekindDomain/IntegerRing.lean
```

### LSP Tools (Recommended for AI Agents)

This project has Lean LSP enabled. Use these tools for efficient verification:

- **lsp_diagnostics**: Check for errors/warnings before committing
- **lean-lsp_lean_goal**: Get proof goals at cursor position
- **lean-lsp_lean_hover_info**: Get type signature and docs for symbols
- **lean-lsp_lean_loogle**: Search Mathlib by type signature
- **lean-lsp_lean_state_search**: Find lemmas to close current goal
- **lean-lsp_lean_leansearch**: Natural language search in Mathlib

### Running the CI Locally

```bash
# The CI uses leanprover/lean-action@v1 - equivalent to:
lake build
```

### Editor Integration

This project is designed to work with VS Code + Lean 4 extension or Neovim + lean.nvim.
The LSP is configured via the lake build system.

## Code Style Guidelines

### File Organization

- One main `.lean` file per logical unit (e.g., `IntegerRing.lean`, `Basic.lean`)
- Main entry point is `DedekindDomain.lean` which imports all modules
- Use `section` to group related definitions within files
- Close sections and namespaces explicitly with `end`

### Naming Conventions

- **Files**: CamelCase (e.g., `IntegerRing.lean`, not `integer_ring.lean`)
- **Definitions/Theorems**: `snake_case` (e.g., `theorem_10_3_normEuclidean`)
- **Constants/Variables**: Lowercase with underscores
- **Types**: Start with capital (e.g., `R`, `K`, `ℕ`)
- **Use unicode**: Lean supports Unicode; prefer mathematical symbols:
  - `→` for function arrows
  - `∀` for "for all"
  - `∃` for "exists"
  - `↔` for iff
  - `∈` for membership
  - `∧` for and, `∨` for or
  - `≠` for not equal

### Import Style

```lean
import Mathlib                    -- external mathlib
import DedekindDomain.Basic        -- local imports
```

- Put `Mathlib` import first
- Then local imports in dependency order
- Avoid importing unused modules

### Proof Structure

```lean
-- Docstring with theorem statement
/-- Theorem X.Y: Description of what is being proved. -/
theorem theorem_X_Y
    (hypothesis : hypothesis_type)
    (another_hypothesis : another_type)
    (hConstraint : condition) :
    conclusion := by
  -- proof tactics here
  sorry  -- temporary placeholder
```

### Common Patterns in This Project

- **Theorems**: `theorem theorem_10_X_description` — numbered to match lecture content
- **Definitions**: `def IsEuclideanFunction`, `def IsEuclideanDomain`
- **Lemmas**: Use `lemma` for intermediate results
- **Variables**: Declare with `variable {R : Type*} [CommRing R]`
- **Namespace**: Wrap in `namespace DedekindDomain` ... `end DedekindDomain`

### Documentation

Every definition and theorem should have a docstring:

```lean
/-- Description of what this defines or states. -/
def myDefinition : Type := ...
```

Use `/-! ... -/` for module-level documentation blocks.

### Error Handling

Lean has no runtime error handling — proofs either compile or they don't.
- Use `sorry` as a temporary placeholder during development
- Never leave `sorry` in final proofs
- Use `admit` with caution (equivalent to `sorry`)

### Lean Options (from lakefile.toml)

This project uses:
- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- `relaxedAutoImplicit = false` — strict implicit inference
- `weak.linter.mathlibStandardSet = true` — mathlib linting rules
- `maxSynthPendingDepth = 3` — implicit synthesis depth limit

## Architecture Notes

- This is a mathematical formalization project (Dedekind domains)
- Content follows lecture structure (`Lecture10`, `Lecture11`, etc.)
- `IntegerRing.lean` contains main definitions about Euclidean domains
- Blueprint for web documentation is in `blueprint/` directory

## Common Tasks

### Adding a New Theorem

1. Add to appropriate file (e.g., `IntegerRing.lean` for Euclidean domain content)
2. Follow naming: `theorem theorem_X_Y_description`
3. Add docstring with theorem number reference
4. Provide proof or `sorry` placeholder

### Building Documentation

```bash
# Build the blueprint web documentation
cd blueprint && make
```

## Git Workflow

- Commit messages should describe mathematical content
- CI runs `lake build` on every push/PR
- No pre-commit hooks configured

---

*Generated for AI agent consumption. Last updated: 2026-02-26*
