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
cd docker && ./rebuild.sh     # Rebuild and restart
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
   - `subgroup_group`: lifts a `Subgroup G H` into a full `Group` using sigma types
   - Proven utility lemmas: `gpow_nat_add`, `gpow_mul`, `gpow_nat_inv_eq`, `gpow_nat_comm`, `inv_inv`, `inv_op`, `inv_e`

3. **Concrete instances**: `Z_add_group` and `Z_cyclic_group` instantiate the abstract structures for integers under addition.

4. **Key admitted theorems** (not yet proven):
   - `generator_order`: g^m = e in an order-m cyclic group
   - `subgroup_of_cyclic`: every subgroup of a cyclic group is cyclic with order dividing the original
   - `gpow_add` (integer exponent addition)

### `galois_theory.v` — Placeholder (empty)

Future home of field extensions, automorphism groups, and the fundamental theorem of Galois theory.

## Rocq Conventions in This Codebase

- All docstrings and inline comments are written in Japanese.
- Sigma types (`{x : T | P x}`) are used for subgroup carriers; `sig_eq` handles equality via proof irrelevance.
- The `omega` / `lia` tactic handles linear arithmetic over integers/naturals throughout.
- `Admitted` is used intentionally to mark theorems planned for future proof — do not remove admissions without completing the proof.
- Concrete group instances (`Z_add_group`, `Z_cyclic_group`, `subgroup_group`) use `Defined` (not `Qed`) so they are computationally transparent and can be reduced by `Eval compute`.
- Each definition or theorem is preceded by a Japanese comment block explaining the mathematical concept and the proof strategy.

## External Resources

- Rocq Standard Library
  - <https://rocq-prover.org/doc/V9.1.0/refman-stdlib/index.html>
  - <https://rocq-prover.org/doc/V9.1.0/stdlib/index.html>
