# Lambda Formalizations in Lean 4

This repository contains Lean 4 ports of formalizations previously developed in Isabelle/HOL.

## Formalizations

* `LambdaEnv` — complete through weak-reduction confluence.
* `LambdaPEnv` planned.

## Project Structure

```text
lambda-formalizations/
├── LambdaEnv/
├── LambdaEnv.lean
├── LambdaFormalizations.lean
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── AGENTS.md
├── progress-lambdaenv.md
└── README.md
```

## Build

From the project root, run:

```bash
lake exe cache get
lake build
```

For focused checks of the final layers:

```bash
lake env lean LambdaEnv/ParallelReduction.lean
lake env lean LambdaEnv/BetaModuloSigma.lean
lake env lean LambdaEnv/WeakReduction.lean
```

## Source Correspondence

The `LambdaEnv` development is based on the Isabelle/HOL theory:

```text
LambdaEnv.thy
```

The Lean 4 development is a port of the Isabelle/HOL `LambdaEnv.thy` theory.
Its public entry point is `LambdaEnv.lean`, which imports syntax, reduction
relations, sigma normalization, parallel reduction, beta modulo sigma, and
weak reduction in dependency order.

### LambdaEnv coverage

The completed port includes:

* syntax and the `term_length` measure;
* sigma reduction, its termination and confluence, and `sigmaNormalize`;
* parallel reduction, Lemma 3.11 composition compatibility, Lemma 3.13's
  star theorem, and strong confluence;
* beta modulo sigma, its two-way multi-step correspondence with parallel
  reduction, and confluence;
* Hardin's forward-confluence method and confluence of weak reduction.

See `progress-lambdaenv.md` for the detailed Isabelle-to-Lean correspondence
and the Isabelle-specific auxiliary declarations not exposed as separate Lean
API.

## Development Policy

* Preserve the mathematical meaning of the Isabelle/HOL formalization.
* Keep the project free of `sorry`, `admit`, and unproven axioms.
* Run `lake build` after substantive changes.
* Record progress in `progress-lambdaenv.md`.
* Do not commit the `.lake` directory.

## Multi-PC Workflow

Each computer should have its own clone under the WSL2 Linux filesystem:

```text
/home/nisizaki/prog0/lambda-formalizations
```

Use GitHub to synchronize changes between computers.

Before starting work:

```bash
git status
git pull --ff-only
```

After finishing work:

```bash
lake build
git status
git add .
git commit -m "Describe the completed work"
git push
```
