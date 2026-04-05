# Proof Progress: fp_factor_theorem (Fp上の因数定理)

## Status Overview
- Overall: Complete
- Complete Lemmas: 5/5
- Unproven (`Admitted`): なし
- Failed/Abandoned Items: なし

## Completed Lemmas

### 定義: `poly_divides_linear`

```coq
Definition poly_divides_linear (F : Field)
    (f : list (ring_carrier F)) (a : ring_carrier F) : Prop :=
  exists q : list (ring_carrier F),
    forall x : ring_carrier F,
      poly_eval F f x =
      ring_mul F (ring_add F x (ring_neg F a)) (poly_eval F q x).
```

### `poly_factor_of_root`

```coq
Lemma poly_factor_of_root :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_eval F f a = ring_zero F ->
    poly_divides_linear F f a.
Proof.
  intros F f a Hroot.
  unfold poly_divides_linear.
  exists (poly_synthetic_div F f a).
  intros x.
  rewrite (poly_remainder_theorem F f a x).
  rewrite Hroot.
  apply ring_add_zero_r.
Qed.
```

### `poly_root_of_factor`

```coq
Lemma poly_root_of_factor :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_divides_linear F f a ->
    poly_eval F f a = ring_zero F.
Proof.
  intros F f a [q Hq].
  rewrite (Hq a).
  rewrite ring_add_neg_r.
  apply ring_mul_zero_l.
Qed.
```

### `factor_theorem` (主定理)

```coq
Theorem factor_theorem :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_divides_linear F f a <-> poly_eval F f a = ring_zero F.
Proof.
  intros F f a.
  split.
  - apply poly_root_of_factor.
  - apply poly_factor_of_root.
Qed.
```

### `fp_factor_theorem` (系)

```coq
Corollary fp_factor_theorem :
  forall (p : nat) (Hp : prime (Z.of_nat p))
         (f : list (ring_carrier (znz_p_field p Hp)))
         (a : ring_carrier (znz_p_field p Hp)),
    poly_divides_linear (znz_p_field p Hp) f a <->
    poly_eval (znz_p_field p Hp) f a = ring_zero (znz_p_field p Hp).
Proof.
  intros p Hp f a.
  apply factor_theorem.
Qed.
```

## Proof Attempts & Diagnostics

特記事項なし。全て一発で証明できた。

## TODO
(すべて完了)
