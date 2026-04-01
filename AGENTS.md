# Repository Guidelines

## Project Structure & Module Organization
`LowRankUnivariateSOS.lean` is the library entry point. Core proof files live in [`LowRankUnivariateSOS/`](./LowRankUnivariateSOS): `PolynomialModel.lean` and `Socp.lean` define the formal model, `UnivariateAlgebraCore.lean`, `UnivariateSOS.lean`, and `UnivariateAlgebra.lean` build the algebraic reductions, and `RankTwoMain.lean` contains the main theorem. Keep new lemmas near the stage of the proof they support instead of growing `RankTwoMain.lean`. Repository docs live in `README.md` and `docs/` (for example `docs/dependency-graph.svg`).

## Build, Test, and Development Commands
Use Lake from the repository root:

```bash
lake build
lake env lean LowRankUnivariateSOS/RankTwoMain.lean
lake update
uvx leanblueprint all
```

`lake build` is the main local regression check and mirrors CI. `lake env lean ...` is useful for checking one file with the pinned toolchain. `lake update` refreshes dependency metadata when intentionally moving mathlib or Lean versions.

## Blueprint Workflow
If you work on blueprint material, use `leanblueprint` through `uvx`, not a global install. Run `uvx leanblueprint all` to regenerate the full blueprint output from the repository root, and use the same `uvx leanblueprint ...` pattern for other subcommands. Keep blueprint-oriented edits scoped with the theorem or module they document so the prose and formalization stay aligned.

## Coding Style & Naming Conventions
This is a Lean 4 project pinned to `leanprover/lean4:v4.29.0` with mathlib `v4.29.0`. Follow existing mathlib-style formatting: two-space indentation in tactic blocks, one declaration per theorem/definition, and short explanatory docstrings for public lemmas. Prefer descriptive theorem names such as `factor_peeling_certificate_step`; use `private theorem` for local helpers. Keep imports minimal and ordered by dependency. The repository enables `weak.linter.mathlibStandardSet = true` and `relaxedAutoImplicit = false`, so write explicit binders and avoid relying on implicit auto parameters.

## Testing Guidelines
There is no separate `tests/` directory; successful compilation is the test suite. Run `lake build` before opening a PR, and rerun `lake env lean <file>` on any module you touched. When adding a theorem, verify downstream files still compile, especially [`LowRankUnivariateSOS.lean`](./LowRankUnivariateSOS.lean), which is the umbrella import for the library.

## Commit & Pull Request Guidelines
Use short, imperative commit subjects such as `Prove coprime residual lemma` or `Refactor factor peeling setup`. Keep commits scoped to one proof step or module. PRs should describe the theorem-level change, list affected files, note any dependency or toolchain updates, and include the local command used to verify the change (`lake build` at minimum). Screenshots are unnecessary unless documentation assets in `docs/` change.
