# Proof Progress: znz_units_group_cyclic_iso

## Status Overview
- Overall: **Complete**
- Complete Lemmas: 10/10
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `primitive_root_generates_all`
```coq
Lemma primitive_root_generates_all :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (g : carrier (znz_units_group p Hp)),
    mult_order_p p Hp Hprime g = (p - 1)%nat ->
    forall x : carrier (znz_units_group p Hp),
      exists k : Z, gpow (znz_units_group p Hp) g k = x.
Proof.
  intros p Hp Hprime g Hg x.
  assert (Hp1 : (0 < p - 1)%nat) by lia.
  assert (Hx_e : gpow_nat (znz_units_group p Hp) x (p - 1) =
                 e (znz_units_group p Hp)) by
    exact (fermat_little_theorem p Hp Hprime x).
  destruct (order_d_elements_are_powers p Hp Hprime g (p - 1) Hp1 Hg x Hx_e)
    as [k [_ Heq]].
  exists (Z.of_nat k).
  rewrite gpow_of_nat.
  exact Heq.
Qed.
```

### `znz_units_cyclic_group`
```coq
Definition znz_units_cyclic_group (p : nat) (Hp : (1 < p)%nat)
    (Hprime : prime (Z.of_nat p)) : CyclicGroup.
Proof.
  set (g := epsilon (inhabits (e (znz_units_group p Hp)))
    (fun g => mult_order_p p Hp Hprime g = (p - 1)%nat)).
  assert (Hg : mult_order_p p Hp Hprime g = (p - 1)%nat).
  { unfold g. apply epsilon_spec. exact (primitive_root_exists p Hp Hprime). }
  refine {|
    cyclic_group := znz_units_group p Hp;
    generator    := g
  |}.
  exact (primitive_root_generates_all p Hp Hprime g Hg).
Defined.
```

### `generator_mult_order_eq_group_order`
```coq
Lemma generator_mult_order_eq_group_order :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n),
    mult_order C n Hord (generator C) = n.
```

### `cyclic_powers_injective`
```coq
Lemma cyclic_powers_injective :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n)
         (r1 r2 : nat),
    (r1 < n)%nat -> (r2 < n)%nat ->
    gpow_nat C (generator C) r1 = gpow_nat C (generator C) r2 -> r1 = r2.
```

### `gpow_nat_mod`
```coq
Lemma gpow_nat_mod :
  forall (G : Group) (g : carrier G) (n k : nat),
    (0 < n)%nat -> gpow_nat G g n = e G ->
    gpow_nat G g (k mod n) = gpow_nat G g k.
```

### `cyc_index` + `cyc_index_spec`
```coq
Definition cyc_index (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n)
    (x : carrier C) : nat :=
  epsilon (inhabits 0%nat) (fun r : nat =>
    (r < n)%nat /\ gpow_nat C (generator C) r = x).

Lemma cyc_index_spec :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n) (x : carrier C),
    (cyc_index C n Hord x < n)%nat /\
    gpow_nat C (generator C) (cyc_index C n Hord x) = x.
```

### `cyc_index_unique`
```coq
Lemma cyc_index_unique :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n)
         (x : carrier C) (r : nat),
    (r < n)%nat -> gpow_nat C (generator C) r = x ->
    r = cyc_index C n Hord x.
```

### `cyc_index_homo`
```coq
Lemma cyc_index_homo :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n) (x y : carrier C),
    (cyc_index C n Hord (op C x y) =
     (cyc_index C n Hord x + cyc_index C n Hord y) mod n)%nat.
```

### `cyclic_group_isomorphic_znz`
```coq
Theorem cyclic_group_isomorphic_znz :
  forall (C : CyclicGroup) (n : nat) (Hn : (0 < n)%nat) (Hord : GroupOrder C n),
    C ≅ znz_group n Hn.
```

### `znz_units_group_cyclic_iso` (主定理)
```coq
Theorem znz_units_group_cyclic_iso :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p)),
    exists Hp1 : (0 < p - 1)%nat,
      znz_units_group p Hp ≅ znz_group (p - 1) Hp1.
```

## Key Technical Pitfalls Encountered

1. **Prop-existential → Type**: `destruct (primitive_root_exists ...)` fails to build a CyclicGroup (Type).
   Fix: use `epsilon` to extract the primitive root from the Prop-existential.

2. **Z_scope pollution**: Nat expressions like `(r + s) mod n` in Z_scope get parsed as Z.
   Fix: explicit `%nat` annotations on all nat arithmetic in lemma statements and proofs.

3. **`gpow_of_nat` direction**: `rewrite gpow_of_nat` fails when goal has `gpow_nat`; need `rewrite <- gpow_of_nat`.

4. **`sig_eq` direction**: `apply sig_eq in H` fails on sigma equality; use `injection H as H` instead.

5. **`Nat2Z.inj_lt` is an iff**: Use `proj1 (Nat2Z.inj_lt _ _)` or `proj2 (Nat2Z.inj_lt _ _)` as appropriate.

6. **`generator C` vs `set g`**: After `set (g := generator C)`, need `fold g` to unify `generator C` with `g` in goals.

7. **`gpow_nat_mod` rewrite scope**: When `k mod n` appears in goal, `rewrite Hk` (where Hk : k = ...) rewrites both occurrences. Use `set` to fix `r := k mod n` before rewriting.

## TODO
- (all done)
