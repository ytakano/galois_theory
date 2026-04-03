---
name: rocq-prover
description: Use this skill when the user wants to prove theorems, lemmas, definitions, or propositions in Rocq/Coq. Activated when the user mentions proving, verifying, or formalizing mathematical statements in Rocq or Coq.
---

# Rocq/Coq Prover

This skill guides you through proving theorems and lemmas in Rocq/Coq by proposing auxiliary lemmas, proof strategies, and tracking progress across sessions.

## Key Files and Directories

| Path | Purpose |
|------|---------|
| `progress/` | Directory for storing all proof progress and planning files |
| `progress/<name>_plan.md` | Proof strategy and proposed lemmas for a given theorem/lemma |
| `progress/<name>_progress.md` | Completed proofs and remaining TODOs for a given theorem/lemma |

Replace `<name>` with the theorem or lemma name (e.g., `nat_add_comm_plan.md`).

---

## Workflow

### Step 1: Plan — Propose a Proof Strategy

When the user presents a theorem or lemma to prove:

1. Check whether `progress/<name>_plan.md` already exists.
   - If it **does not exist**, create it and proceed to step 2.
   - If it **exists**, read it and skip to Step 2.
2. Analyze the goal and propose:
   - A high-level proof strategy
   - A list of auxiliary lemmas needed
   - The recommended order in which to prove them
3. Write the proposal to `progress/<name>_plan.md` using the template below.
4. Proceed to Step 2.

**`<name>_plan.md` template:**
```markdown
# Proof Plan: <Theorem/Lemma Name>

## Goal
<State the theorem or lemma to be proved>

## Proof Strategy
<Describe the overall approach>

## Proposed Lemmas
- [ ] `lemma_1`: <description>
- [ ] `lemma_2`: <description>
...

## Proof Order
1. `lemma_1`
2. `lemma_2`
...
N. `<name>` (main goal)
```

---

### Step 2: Prove — Work Through Lemmas One at a Time

1. Read `progress/<name>_plan.md` to review the strategy and lemma list.
   - If the file does not exist, return to Step 1.
2. Read `progress/<name>_progress.md` if it exists, to check what has already been proved and what TODOs remain.
3. Select **one** unproved lemma and attempt to prove it.
4. Verify the proof by running:
   ```
   rocq compile <filename>
   ```
   - If compilation succeeds, record the completed proof in `progress/<name>_progress.md`.
   - If compilation fails, diagnose the error, revise the proof, and retry.
5. Update `progress/<name>_progress.md` with the result and remaining TODOs.
6. Repeat from step 3 until all lemmas are proved, then proceed to Step 3.

**`<name>_progress.md` template:**
~~~markdown
# Proof Progress: <Theorem/Lemma Name>

## Completed Lemmas
### `lemma_1`

```coq
<proof code>
```

## TODO
- [ ] `lemma_2`
- [ ] `<name>` (main goal)
~~~

---

### Step 3: Conclude — Prove the Main Theorem or Lemma

1. Read `progress/<name>_plan.md` to recall the overall strategy.
2. Read `progress/<name>_progress.md` to confirm all required lemmas are proved.
3. Using the completed lemmas, write and verify the proof of the main theorem or lemma.
4. Verify with:
   ```
   rocq compile <filename>
   ```
   - If compilation succeeds, record the final proof in `progress/<name>_progress.md` and mark the goal as complete.
   - If compilation fails, analyze the failure, revise the strategy or add new lemmas as needed, update `progress/<name>_plan.md`, and return to Step 2.

---

## Proof Verification

All proofs must be verified by successful compilation:

```bash
rocq compile <filename>
```

A proof is considered complete only when there are **no compilation errors**. If errors occur, treat them as evidence of an incorrect or incomplete proof and revise accordingly.

---

## Notes

- Although this skill uses "theorem" and "lemma" throughout, the same workflow applies to **any provable Rocq/Coq construct**: definitions, propositions, instances, etc.
- Name your progress files after the specific construct being proved (e.g., `progress/myDef_plan.md` for a definition named `myDef`).
- Keep each `_plan.md` and `_progress.md` pair focused on a single named goal to avoid confusion across related proofs.