# Copilot Instructions

## Project Overview

A Coq/Rocq formalization of Galois Theory, built bottom-up from number theory through group theory toward the full Galois correspondence. This is an AI-assisted formal mathematics experiment.

## Build & Verify

```bash
rocq compile integer.v        # Compile main formalization
rocq compile galois_theory.v  # Compile Galois theory file (currently empty)
rocq repl integer.v           # Interactive exploration REPL
```

A proof is accepted only when `rocq compile` produces **no errors**. There is no test suite — compilation is the verification step.

## Architecture

All current work lives in `integer.v`, organized in layers:

1. **Number theory** — GCD (`gcd_euclidean`), congruences (`cong_*`), linear Diophantine equations (`linear_diophantine`)
2. **Abstract group theory** — `Group` record (carrier set, binary op, identity, inverse, five axioms); `gpow_nat`/`gpow` for natural/integer exponents; `CyclicGroup`, `GroupIsomorphism`/`GroupIsomorphic` (≅), `GroupOrder`, `Subgroup`/`subgroup_group`
3. **Concrete instances** — `Z_add_group`, `Z_cyclic_group` (integers under addition)
4. `galois_theory.v` — placeholder for field extensions and the Galois correspondence

`progress/` holds proof planning and tracking files (see Proof Workflow below). Root-level `generator_order.md` and `generator_order_progress.md` are legacy files — ignore them.

## Proof Workflow

Always follow the three-step workflow for any new proof:

1. **Plan** — Create `progress/<theorem>_plan.md` decomposing the goal into sub-lemmas and recording strategy before writing any Rocq.
2. **Sub-lemmas** — Prove one sub-lemma at a time; update `progress/<theorem>_progress.md` after each. Use `Admitted` for unproven steps to keep the file compiling.
3. **Assemble** — Once all sub-lemmas compile, prove the top-level theorem and mark it complete.

Use `/clear` between sub-lemma proofs to manage context limits. The progress files persist state across sessions.

## Key Conventions

- **All comments and docstrings are written in Japanese.** Every definition and theorem is preceded by a Japanese comment block explaining the mathematical concept and proof strategy.
- **`Admitted` is intentional.** It marks theorems planned for future proof. Do not remove an `Admitted` without completing the proof.
- **Concrete instances use `Defined`, not `Qed`**, to remain computationally transparent for `Eval compute` reduction (`Z_add_group`, `Z_cyclic_group`, `subgroup_group`).
- **Subgroup carriers use sigma types** (`{x : T | P x}`); `sig_eq` handles equality via proof irrelevance.
- **Linear arithmetic** is handled by `omega`/`lia` throughout.
- **Reasoning depth** — Before responding, assess complexity: *simple* (direct response), *moderate* (brief think-through), *complex* (break into sub-problems). State the assessment explicitly.

## External References

- Rocq Standard Library: https://rocq-prover.org/doc/V9.1.0/refman-stdlib/index.html
- Rocq stdlib index: https://rocq-prover.org/doc/V9.1.0/stdlib/index.html
