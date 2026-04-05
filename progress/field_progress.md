# Proof Progress: Field (体) の定義

## Status Overview
- Overall: In Progress
- Complete Lemmas: 13/16
- Unproven (`Admitted`): `znz_p_field`
- Failed/Abandoned Items: なし

## Completed Lemmas

### `Ring` Record (line 3860)
```coq
Record Ring : Type := {
  ring_carrier : Type;
  ring_add : ring_carrier -> ring_carrier -> ring_carrier;
  ring_zero : ring_carrier;
  ring_neg  : ring_carrier -> ring_carrier;
  ring_mul  : ring_carrier -> ring_carrier -> ring_carrier;
  ring_one  : ring_carrier;
  ring_add_assoc : ...; ring_add_comm : ...; ring_add_zero_l : ...; ring_add_neg_l : ...;
  ring_mul_assoc : ...; ring_mul_one_l : ...; ring_mul_one_r : ...;
  ring_distr_l : ...; ring_distr_r : ...
}.
```

### `ring_add_zero_r`
```coq
Lemma ring_add_zero_r : forall (R : Ring) (a : ring_carrier R),
  ring_add R a (ring_zero R) = a.
(* rewrite ring_add_comm; apply ring_add_zero_l. *)
```

### `ring_add_neg_r`
```coq
Lemma ring_add_neg_r : forall (R : Ring) (a : ring_carrier R),
  ring_add R a (ring_neg R a) = ring_zero R.
(* rewrite ring_add_comm; apply ring_add_neg_l. *)
```

### `ring_add_cancel_l`
```coq
Lemma ring_add_cancel_l : forall (R : Ring) (a b c : ring_carrier R),
  ring_add R a b = ring_add R a c -> b = c.
(* 左から (-a) を加え、結合律・左逆元・左零元を適用 *)
```

### `ring_mul_zero_l`
```coq
Lemma ring_mul_zero_l : forall (R : Ring) (a : ring_carrier R),
  ring_mul R (ring_zero R) a = ring_zero R.
(* ring_add_cancel_l + ring_distr_r *)
```

### `ring_mul_zero_r`
```coq
Lemma ring_mul_zero_r : forall (R : Ring) (a : ring_carrier R),
  ring_mul R a (ring_zero R) = ring_zero R.
(* ring_add_cancel_l + ring_distr_l *)
```

### `ring_neg_neg`
```coq
Lemma ring_neg_neg : forall (R : Ring) (a : ring_carrier R),
  ring_neg R (ring_neg R a) = a.
(* ring_add_cancel_l + ring_add_neg_r + ring_add_neg_l *)
```

### `ring_neg_mul_l`
```coq
Lemma ring_neg_mul_l : forall (R : Ring) (a b : ring_carrier R),
  ring_mul R (ring_neg R a) b = ring_neg R (ring_mul R a b).
(* ring_add_cancel_l + ring_distr_r + ring_add_neg_r + ring_mul_zero_l *)
```

### `ring_neg_mul_r`
```coq
Lemma ring_neg_mul_r : forall (R : Ring) (a b : ring_carrier R),
  ring_mul R a (ring_neg R b) = ring_neg R (ring_mul R a b).
(* ring_add_cancel_l + ring_distr_l + ring_add_neg_r + ring_mul_zero_r *)
```

### `Field` Record (line 4012)
```coq
Record Field : Type := {
  field_ring :> Ring;
  field_inv : ring_carrier field_ring -> ring_carrier field_ring;
  field_mul_comm : forall a b, ring_mul field_ring a b = ring_mul field_ring b a;
  field_inv_l : forall x, x <> ring_zero field_ring ->
    ring_mul field_ring (field_inv x) x = ring_one field_ring;
  field_one_ne_zero : ring_one field_ring <> ring_zero field_ring
}.
```

### `field_inv_r`
```coq
Lemma field_inv_r : forall (F : Field) (x : ring_carrier F),
  x <> ring_zero F -> ring_mul F x (field_inv F x) = ring_one F.
(* field_mul_comm + field_inv_l *)
```

### `field_inv_nonzero`
```coq
Lemma field_inv_nonzero : forall (F : Field) (x : ring_carrier F),
  x <> ring_zero F -> field_inv F x <> ring_zero F.
(* inv(x) = 0 → inv(x)*x = 0*x = 0 ≠ 1 矛盾 *)
```

### `field_no_zero_divisors`
```coq
Lemma field_no_zero_divisors : forall (F : Field) (a b : ring_carrier F),
  ring_mul F a b = ring_zero F -> a = ring_zero F \/ b = ring_zero F.
(* classic + inv(a)*(a*b) = 0 → (inv(a)*a)*b = 0 → b = 0 *)
```

### `field_mul_cancel_l`
```coq
Lemma field_mul_cancel_l : forall (F : Field) (a b c : ring_carrier F),
  a <> ring_zero F -> ring_mul F a b = ring_mul F a c -> b = c.
(* inv(a) を両辺に掛けて ring_mul_assoc + field_inv_l + ring_mul_one_l *)
```

### `field_div` (定義)
```coq
Definition field_div (F : Field) (a b : ring_carrier F) : ring_carrier F :=
  ring_mul F a (field_inv F b).
```

### `znz_prime_nonzero_coprime`
```coq
Lemma znz_prime_nonzero_coprime : forall (p : nat) (a : Z),
  prime (Z.of_nat p) -> a mod Z.of_nat p <> 0 ->
  Z.gcd (a mod Z.of_nat p) (Z.of_nat p) = 1.
(* Zis_gcd_gcd + Zis_gcd_sym + prime_rel_prime *)
```

## Proof Attempts & Diagnostics

### `znz_p_field` — Status: Admitted

- 課題: `field_inv` の型不整合
  - `ring_carrier = Z` だが `znz_units_inv_val` が期待する型は
    `{x : Z | 0 <= x < p /\ gcd(x,p) = 1}` (sigma 型)
  - 修正方針: carrier を `{x : Z | 0 <= x < Z.of_nat p}` (= `znz_group` の carrier) に変更するか、
    `epsilon` を使った Z → Z の逆元関数を別途定義する

## TODO
- [ ] `znz_p_field`: carrier 型を `znz_group` の sigma 型に合わせて再実装
