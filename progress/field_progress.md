# Proof Progress: Field (体) の定義

## Status Overview
- Overall: Complete
- Complete Lemmas: 16/16
- Unproven (`Admitted`): なし
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

### `znz_field_inv_val` (定義)
```coq
Definition znz_field_inv_val (p : nat) (a : {x : Z | 0 <= x < Z.of_nat p}) : Z :=
  epsilon (inhabits 0%Z)
    (fun b => 0 <= b < Z.of_nat p /\ cong p (proj1_sig a * b) 1).
```

### `znz_field_inv_spec`
```coq
Lemma znz_field_inv_spec : forall (p : nat) (Hp : prime (Z.of_nat p))
    (a : {x : Z | 0 <= x < Z.of_nat p}),
  proj1_sig a <> 0 ->
  0 <= znz_field_inv_val p a < Z.of_nat p /\
  cong p (proj1_sig a * znz_field_inv_val p a) 1.
(* epsilon_spec + znz_prime_nonzero_coprime + znz_coprime_bezout_inv + Z.mod_small *)
```

### `znz_p_ring`
```coq
Definition znz_p_ring (p : nat) (Hp : prime (Z.of_nat p)) : Ring.
(* carrier: {x : Z | 0 <= x < Z.of_nat p}, 全演算は mod p で正規化 *)
(* ring_one := exist _ (1 mod p) ...; ring_add_assoc: Zplus_mod_idemp_*; ring_mul_assoc: Zmult_mod_idemp_* *)
```

### `znz_p_field` (2025-XX-XX 証明完了)
```coq
Definition znz_p_field (p : nat) (Hp : prime (Z.of_nat p)) : Field.
(* field_ring := znz_p_ring p Hp
   field_inv := fun a => match Z.eq_dec (proj1_sig a) 0 with
     | left _ => exist _ 0 ...
     | right Ha => exist _ (znz_field_inv_val p a) ...
     end
   field_mul_comm: rewrite Z.mul_comm; reflexivity
   field_inv_l: cbn [proj1_sig] + znz_field_inv_spec + Z.mul_comm + Z.mod_add
   field_one_ne_zero: proj1_sig ring_one = proj1_sig ring_zero → simpl + Z.mod_small + lia *)
```

## Proof Attempts & Diagnostics

### `znz_p_field` — Status: Complete (previously Admitted)

- 旧課題: `field_inv` の型不整合 (carrier = Z と sigma 型の不整合)
- 解決: carrier を `{x : Z | 0 <= x < Z.of_nat p}` に変更
- 重要な落とし穴:
  - `proj1_sig (exist _ (znz_field_inv_val p x) ...)` は `cbn [proj1_sig]` で簡約必要
  - `f_equal proj1_sig` は implicit 引数の問題で失敗 → `assert H; rewrite Heq` を使う
  - `rewrite Z.mod_add` 後のゴールは `1 mod p = 1 mod p` なので `reflexivity`（`apply Z.mod_small` ではない）
  - `field_mul_comm` のゴールは already `(a*b) mod p = (b*a) mod p` なので `rewrite Z.mul_comm; reflexivity`

## TODO
- なし（全証明完了）
