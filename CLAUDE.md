# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

A Coq/Rocq formalization of Galois Theory. The project is building up from foundational number theory and group theory (in `integer.v`) toward a full formalization of Galois theory (planned in `galois_theory.v`). Described as a Claude Code experiment to explore AI capabilities in advanced formal mathematics.

## Development Environment

The project is containerized. Docker scripts are in `docker/`:

```bash
cd docker && ./build.sh       # Build image
cd docker && ./up_docker.sh   # Start container
cd docker && ./exec_zsh.sh    # Attach shell
cd docker && ./down_docker.sh # Stop container
```

## Compilation

```bash
rocq compile integer.v        # Compile main file
rocq compile galois_theory.v  # Compile Galois theory file
```

Interactive exploration:
```bash
rocq repl integer.v           # Start REPL with file loaded
```

## Code Architecture

### `integer.v` — Main formalization (all current work)

Built in layers, bottom-up:

1. **Number theory**: GCD via Euclidean algorithm (`gcd_euclidean`), congruences (`cong_*`), linear Diophantine equations (`linear_diophantine`).

2. **Group theory**: Abstract `Group` record with carrier set, binary operation, identity, inverse, and five axioms. Key derived constructs:
   - `gpow_nat` / `gpow`: group power for natural and integer exponents
   - `CyclicGroup`: groups with a generator whose powers cover all elements
   - `GroupIsomorphism` / `GroupIsomorphic` (≅ notation): homomorphism + bijection
   - `GroupOrder`: finite group size via bijection to `Fin.t n`
   - `Subgroup`: predicate-based subgroup definition with closure requirements

3. **Concrete instances**: `Z_add_group` and `Z_cyclic_group` instantiate the abstract structures for integers under addition.

4. **Key admitted theorems** (not yet proven):
   - `generator_order`: g^m = e in an order-m cyclic group
   - `subgroup_of_cyclic`: every subgroup of a cyclic group is cyclic with order dividing the original
   - `gpow_add` (integer exponent addition)

### `galois_theory.v` — Placeholder (empty)

Future home of field extensions, automorphism groups, and the fundamental theorem of Galois theory.

## Rocq Conventions in This Codebase

- Sigma types (`{x : T | P x}`) are used for subgroup carriers; `sig_eq` handles equality via proof irrelevance.
- The `omega` tactic handles linear arithmetic over integers/naturals throughout.
- `Admitted` is used intentionally to mark theorems planned for future proof — do not remove admissions without completing the proof.
