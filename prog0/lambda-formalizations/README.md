# Lambda Formalizations in Lean 4

This repository contains Lean 4 ports of formalizations previously developed in Isabelle/HOL.

## Formalizations

* `LambdaEnv`
* `LambdaPEnv` planned

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

## Source Correspondence

The `LambdaEnv` development is based on the Isabelle/HOL theory:

```text
LambdaEnv.thy
```

The Lean 4 files are organized by topic, including syntax, reduction relations, normalization, parallel reduction, and confluence.

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
