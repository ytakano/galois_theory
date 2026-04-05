# Proof Progress: fp_linear_eq_unique_solution

## Status Overview
- Overall: Complete
- Complete Lemmas: 4/4
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `field_linear_eq_solution`

```coq
Lemma field_linear_eq_solution : forall (F : Field) (a b : ring_carrier F),
  a <> ring_zero F ->
  ring_add F (ring_mul F a (ring_neg F (ring_mul F (field_inv F a) b))) b = ring_zero F.
Proof.
  intros F a b Ha.
  rewrite ring_neg_mul_r.
  rewrite <- ring_mul_assoc.
  rewrite field_inv_r by exact Ha.
  rewrite ring_mul_one_l.
  apply ring_add_neg_l.
Qed.
```

注意: 最初のスクリプトに `rewrite <- ring_neg_mul_l` を余分に含めていたため
"Found no subterm matching" エラーが発生した。この行を削除して解決。

### `field_linear_eq_unique`

```coq
Lemma field_linear_eq_unique : forall (F : Field) (a b x y : ring_carrier F),
  a <> ring_zero F ->
  ring_add F (ring_mul F a x) b = ring_zero F ->
  ring_add F (ring_mul F a y) b = ring_zero F ->
  x = y.
Proof.
  intros F a b x y Ha Hx Hy.
  apply (field_mul_cancel_l F a).
  - exact Ha.
  - apply (ring_add_cancel_l F b).
    rewrite (ring_add_comm F b), (ring_add_comm F b).
    rewrite Hx, Hy.
    reflexivity.
Qed.
```

### `field_linear_eq_unique_solution` (主定理)

```coq
Theorem field_linear_eq_unique_solution : forall (F : Field) (a b : ring_carrier F),
  a <> ring_zero F ->
  exists! x : ring_carrier F,
    ring_add F (ring_mul F a x) b = ring_zero F.
Proof.
  intros F a b Ha.
  exists (ring_neg F (ring_mul F (field_inv F a) b)).
  split.
  - apply field_linear_eq_solution. exact Ha.
  - intros y Hy.
    apply (field_linear_eq_unique F a b).
    + exact Ha.
    + apply field_linear_eq_solution. exact Ha.
    + exact Hy.
Qed.
```

### `fp_linear_eq_unique_solution` (系)

```coq
Corollary fp_linear_eq_unique_solution :
  forall (p : nat) (Hp : prime (Z.of_nat p))
         (a b : ring_carrier (znz_p_field p Hp)),
  a <> ring_zero (znz_p_field p Hp) ->
  exists! x : ring_carrier (znz_p_field p Hp),
    ring_add (znz_p_field p Hp) (ring_mul (znz_p_field p Hp) a x) b =
    ring_zero (znz_p_field p Hp).
Proof.
  intros p Hp a b Ha.
  apply field_linear_eq_unique_solution.
  exact Ha.
Qed.
```

## Proof Attempts & Diagnostics

### `field_linear_eq_solution` — Attempt 1 (失敗)

- Error: `Found no subterm matching "ring_mul ?M1523 ?M1524 (field_inv ?M1523 ?M1524)"`
- Diagnosis: `rewrite <- ring_neg_mul_l` が余分で、目標に `field_inv_r` のパターンを見つけられなかった
- Fix: `rewrite <- ring_neg_mul_l` を削除 → 成功

## TODO
(すべて完了)
