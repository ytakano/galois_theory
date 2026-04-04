# Proof Progress: znz_units_group (既約剰余類群)

## Status Overview
- Overall: Complete
- Complete Lemmas: 6/6
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `znz_gcd_one`

```coq
Lemma znz_gcd_one : forall (n : nat),
  Z.gcd 1 (Z.of_nat n) = 1.
Proof.
  intros n.
  apply Zis_gcd_gcd. lia.
  constructor.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros d Hd1 _. exact Hd1.
Qed.
```

### `znz_gcd_mod_eq`

```coq
Lemma znz_gcd_mod_eq : forall (n : nat) (Hn : (0 < n)%nat) (a : Z),
  Z.gcd (a mod Z.of_nat n) (Z.of_nat n) = Z.gcd a (Z.of_nat n).
Proof.
  intros n Hn a.
  rewrite Z.gcd_mod by lia.
  apply Z.gcd_comm.
Qed.
```

**Key insight**: `Z.gcd_mod` in Rocq 9.1 has the form `Z.gcd (a mod b) b = Z.gcd b a` (NOT `Z.gcd a b = Z.gcd b (a mod b)`).

### `znz_gcd_mul_coprime`

```coq
Lemma znz_gcd_mul_coprime : forall (n : nat) (a b : Z),
  Z.gcd a (Z.of_nat n) = 1 ->
  Z.gcd b (Z.of_nat n) = 1 ->
  Z.gcd (a * b) (Z.of_nat n) = 1.
Proof.
  intros n a b Ha Hb.
  assert (Hra : rel_prime (Z.of_nat n) a).
  { unfold rel_prime. apply Zis_gcd_sym. rewrite <- Ha. apply Zgcd_is_gcd. }
  assert (Hrb : rel_prime (Z.of_nat n) b).
  { unfold rel_prime. apply Zis_gcd_sym. rewrite <- Hb. apply Zgcd_is_gcd. }
  assert (Hr : rel_prime (Z.of_nat n) (a * b)).
  { apply rel_prime_mult; assumption. }
  apply Zis_gcd_gcd. lia.
  apply Zis_gcd_sym. exact Hr.
Qed.
```

### `znz_coprime_bezout_inv`

```coq
Lemma znz_coprime_bezout_inv : forall (n : nat) (Hn : (1 < n)%nat) (a : Z),
  0 <= a < Z.of_nat n ->
  Z.gcd a (Z.of_nat n) = 1 ->
  exists b : Z,
    0 <= b < Z.of_nat n /\
    cong n (a * b) 1 /\
    Z.gcd b (Z.of_nat n) = 1.
```

Key: uses `linear_diophantine` for Bezout coefficients, direct `ring_simplify + lia` for congruence, and `Zis_gcd` for gcd of inverse.

### `znz_units_inv_val` + `znz_units_inv_prop`

```coq
Definition znz_units_inv_val ... := epsilon (inhabits 0%Z) ...
Lemma znz_units_inv_prop ... apply epsilon_spec. ...
```

### `znz_units_group`

```coq
Definition znz_units_group (n : nat) (Hn : (1 < n)%nat) : Group.
```

Carrier: `{x : Z | 0 <= x < Z.of_nat n /\ Z.gcd x (Z.of_nat n) = 1}`
Operation: `[a] * [b] = [a*b mod n]`

## Proof Attempts & Diagnostics

### Issues encountered and fixed:

1. **`Z.gcd_mod` form**: In Rocq 9.1, `Z.gcd_mod` has form `Z.gcd (a mod b) b = Z.gcd b a`.
   Fixed: `rewrite Z.gcd_mod by lia; apply Z.gcd_comm`.

2. **`Z.divide_refl`**: Requires explicit application, use `apply Z.divide_refl` not `exact Z.divide_refl`.

3. **`linarith` not available**: Use `lia` instead throughout.

4. **`|` divisibility in `assert`**: Need parentheses: `assert (H : (n | m))`.

5. **`cong_of_mod` / `mod_of_cong`**: Defined later in the file. Used direct proofs instead:
   - For congruence: `assert Hmod; rewrite Hmod; ring_simplify; lia`
   - For inverse axioms: `unfold cong; destruct; rewrite Heq; Z.mod_add; Z.mod_small`

6. **`cong_trans`**: Defined later in the file. Replaced with direct `ring_simplify + lia` proof.

7. **`ltac:(lia)` in `conj`**: Can fail for conjunctive goals. Use `assert H1n : ...` before `refine` and reference it.

8. **`simpl` expands `1 * a`**: After `apply sig_eq; simpl`, `1 * a` expands to a match expression.
   Fixed: use `cbn [proj1_sig]` then `rewrite Z.mul_1_l/r`.

## TODO
- None: all complete.

## Completion Date
2026-04-04
