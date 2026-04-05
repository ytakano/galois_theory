# Proof Progress: mult_order (乗法位数)

## Status Overview
- Overall: **Complete**
- Complete Lemmas: 12/12
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `element_has_finite_period`

```coq
Lemma element_has_finite_period :
  forall (G : Group) (m : nat) (a : carrier G),
    (0 < m)%nat ->
    GroupOrder G m ->
    exists d : nat, (0 < d)%nat /\ gpow G a (Z.of_nat d) = e G.
Proof.
  intros G m a Hm Hord.
  destruct Hord as [f [Hinj Hsurj]].
  destruct (pigeonhole_Fin m (fun k => f (gpow_nat G a k)))
    as [i [j [Hij [Hjm Heq]]]].
  assert (Hpow : gpow_nat G a i = gpow_nat G a j).
  { apply Hinj. exact Heq. }
  exists (j - i)%nat.
  split.
  - lia.
  - apply equal_powers_imply_period.
    + exact Hij.
    + rewrite !gpow_of_nat. exact Hpow.
Qed.
```

### `mult_order_exists`

```coq
Lemma mult_order_exists :
  forall (G : Group) (m : nat) (Hm : GroupOrder G m) (a : carrier G),
    exists d : nat,
      (0 < d)%nat /\
      gpow G a (Z.of_nat d) = e G /\
      forall d' : nat,
        (0 < d')%nat -> gpow G a (Z.of_nat d') = e G -> (d <= d')%nat.
```
Key: use `group_order_pos` + `element_has_finite_period` for existence; `well_ordering_nat` for minimum; `classic (d' < d)` for monotonicity direction.

### `mult_order` (Definition)

```coq
Definition mult_order (G : Group) (m : nat) (Hm : GroupOrder G m)
    (a : carrier G) : nat :=
  epsilon (inhabits 0%nat) (fun d =>
    (0 < d)%nat /\
    gpow G a (Z.of_nat d) = e G /\
    forall d' : nat,
      (0 < d')%nat -> gpow G a (Z.of_nat d') = e G -> (d <= d')%nat).
```

### `mult_order_spec`

```coq
Lemma mult_order_spec : ...
Proof.
  intros G m Hm a. unfold mult_order.
  apply epsilon_spec. exact (mult_order_exists G m Hm a).
Qed.
```
Key: use `exact (mult_order_exists G m Hm a)` NOT `apply mult_order_exists` — variable `m` is not inferrable after `epsilon_spec`.

### `gpow_nat_period_cancel`

```coq
Lemma gpow_nat_period_cancel :
  forall (G : Group) (a : carrier G) (d k r : nat),
    gpow_nat G a d = e G ->
    gpow_nat G a (d * k + r) = gpow_nat G a r.
Proof.
  intros G a d k r Hd.
  rewrite gpow_nat_add. rewrite gpow_nat_mul. rewrite Hd. rewrite gpow_nat_e. apply id_left.
Qed.
```

### `mult_order_divides` (定理2)

```coq
Theorem mult_order_divides :
  forall (G : Group) (m : nat) (Hm : GroupOrder G m) (a : carrier G) (x : nat),
    gpow_nat G a x = e G <-> Nat.divide (mult_order G m Hm a) x.
```
Key patterns:
- In Z_scope, use `set (q := (x/d)%nat)` and `set (r := (x mod d)%nat)` to force nat arithmetic
- Use `Nat.eq_dec r 0` instead of `classic` for case split on remainder
- ← direction: `rewrite Hk; rewrite Nat.mul_comm; rewrite gpow_nat_mul; rewrite Hd_nat; apply gpow_nat_e`

### `mult_order_powers_distinct` (定理1)

```coq
Theorem mult_order_powers_distinct :
  forall (G : Group) (m : nat) (Hm : GroupOrder G m) (a : carrier G) (i j : nat),
    (i < mult_order G m Hm a)%nat ->
    (j < mult_order G m Hm a)%nat ->
    i <> j ->
    gpow_nat G a i <> gpow_nat G a j.
```
Key: `classic (i < j)` for case split; use `(j-i)%nat` with `%nat` annotation when passing to `Hd_min`.

### `euler_phi_prime`

```coq
Lemma euler_phi_prime : forall (p : nat), prime (Z.of_nat p) -> euler_phi p = (p-1)%nat.
Proof.
  intros p Hp.
  pose proof (euler_phi_prime_pow p 1 Hp (Nat.le_refl 1)) as H.
  rewrite Nat.pow_1_r in H. simpl in H. lia.
Qed.
```

### `prime_units_group_order`

```coq
Lemma prime_units_group_order :
  forall (p : nat) (Hp : (1 < p)%nat), prime (Z.of_nat p) ->
    GroupOrder (znz_units_group p Hp) (p - 1).
Proof.
  intros p Hp Hprime.
  pose proof (euler_phi_group_order p Hp) as H.
  rewrite euler_phi_prime in H by exact Hprime. exact H.
Qed.
```

### `mult_order_p` (Definition)

```coq
Definition mult_order_p (p : nat) (Hp : (1 < p)%nat)
    (Hprime : prime (Z.of_nat p)) (a : carrier (znz_units_group p Hp)) : nat :=
  mult_order (znz_units_group p Hp) (p-1) (prime_units_group_order p Hp Hprime) a.
```

### `mult_order_p_powers_distinct` / `mult_order_p_divides`

Corollaries applying the general theorems with explicit arguments:
```coq
exact (mult_order_powers_distinct (znz_units_group p Hp) (p-1) (prime_units_group_order p Hp Hprime) a i j Hi Hj Hne).
```
Key: `m` and `Hm` are not inferrable from the conclusion — must use `exact` with full explicit arguments, NOT `apply`.

## Proof Attempts & Diagnostics

### Issue: `Nat.le_of_not_lt` not found
- Fix: `destruct (classic (d' < d)) as [Hlt | Hnlt]. exfalso. ... lia.`

### Issue: Z_scope arithmetic conflicts
- `(d | x)%nat` notation fails for nat divisibility: use `Nat.divide d x`
- `d * q + r` in assertions parsed as Z: use `set (q := (x/d)%nat)` pattern
- `(j - i)` in `Hd_min` argument parsed as Z: annotate as `(j - i)%nat`

### Issue: `apply mult_order_exists` after `epsilon_spec`
- `m` not inferrable from goal after `epsilon_spec` strips it
- Fix: `exact (mult_order_exists G m Hm a)` with explicit args

### Issue: Duplicate proof block
- Caused by partial edit that replaced only the `split.` section
- Fix: delete the orphaned `Proof. ... Qed.` block

## TODO

(すべて完了)

## Completion Date
2026-04-05
