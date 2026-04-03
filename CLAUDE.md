# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

A Coq/Rocq formalization of Galois Theory. The project is building up from foundational number theory and group theory (in `integer.v`) toward a full formalization of Galois theory (planned in `galois_theory.v`). Described as a Claude Code experiment to explore AI capabilities in advanced formal mathematics.

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

4. **Additional utility lemmas**: `gpow_nat_e`, `gpow_nat_mul`, `gpow_mul`, `gpow_of_nat`, `gpow_neg_of_nat`, `inv_unique_r`.

5. **Key admitted theorems** (not yet proven):
   - `generator_order`: g^m = e in an order-m cyclic group
   - `subgroup_of_cyclic`: every subgroup of a cyclic group is cyclic with order dividing the original

### `galois_theory.v` — Placeholder (empty)

Future home of field extensions, automorphism groups, and the fundamental theorem of Galois theory.

## Rocq Conventions in This Codebase

- All docstrings and inline comments are written in Japanese.
- Sigma types (`{x : T | P x}`) are used for subgroup carriers; `sig_eq` handles equality via proof irrelevance.
- The `omega` / `lia` tactic handles linear arithmetic over integers/naturals throughout.
- `Admitted` is used intentionally to mark theorems planned for future proof — do not remove admissions without completing the proof.
- Concrete group instances (`Z_add_group`, `Z_cyclic_group`, `subgroup_group`) use `Defined` (not `Qed`) so they are computationally transparent and can be reduced by `Eval compute`.
- Each definition or theorem is preceded by a Japanese comment block explaining the mathematical concept and the proof strategy.

## Reasoning Policy

Before responding to any request, first assess the required reasoning depth:

- **Simple** (e.g., factual lookup, single-file edit): Respond directly.
- **Moderate** (e.g., multi-file refactor, debugging): Think through the approach briefly before acting.
- **Complex** (e.g., architecture design, algorithm design, proof): Use extended reasoning — break the problem into sub-problems, consider trade-offs, then proceed step by step.

Always make your reasoning depth assessment explicit before responding:
> "This is a [simple/moderate/complex] task because ..."

## External Resources

- Rocq Standard Library
  - <https://rocq-prover.org/doc/V9.1.0/refman-stdlib/index.html>
  - <https://rocq-prover.org/doc/V9.1.0/stdlib/index.html>
