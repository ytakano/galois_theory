# Proof Progress: fp_remainder_theorem (Fp上の剰余の定理)

## Status Overview
- Overall: Complete
- Complete Lemmas: 8/8
- Unproven (`Admitted`): なし
- Failed/Abandoned Items: なし

## Completed Lemmas

### 定義: `poly_eval`
```coq
Fixpoint poly_eval (F : Field) (f : list (ring_carrier F)) (x : ring_carrier F)
  : ring_carrier F :=
  match f with
  | [] => ring_zero F
  | c :: cs => ring_add F c (ring_mul F x (poly_eval F cs x))
  end.
```

### 定義: `poly_synthetic_div`
```coq
Fixpoint poly_synthetic_div (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F)
  : list (ring_carrier F) :=
  match f with
  | [] => []
  | _ :: cs =>
    match cs with
    | [] => []
    | _ => poly_eval F cs a :: poly_synthetic_div F cs a
    end
  end.
```

### `poly_eval_nil`, `poly_eval_cons`, `poly_synthetic_div_nil`, `poly_synthetic_div_singleton`, `poly_synthetic_div_cons`
定義から直ちに `reflexivity`。

### `poly_remainder_alg_A`
```coq
Lemma poly_remainder_alg_A : forall (F : Field) (a x e : ring_carrier F),
  ring_add F (ring_mul F (ring_add F x (ring_neg F a)) e) (ring_mul F a e)
  = ring_mul F x e.
Proof.
  intros F a x e.
  rewrite ring_distr_r.
  rewrite ring_neg_mul_l.
  rewrite ring_add_assoc.
  rewrite ring_add_neg_l.
  rewrite ring_add_zero_r.
  reflexivity.
Qed.
```

### `poly_remainder_alg_B`
```coq
Lemma poly_remainder_alg_B : forall (F : Field) (a x q : ring_carrier F),
  ring_mul F x (ring_mul F (ring_add F x (ring_neg F a)) q)
  = ring_mul F (ring_add F x (ring_neg F a)) (ring_mul F x q).
Proof.
  intros F a x q.
  rewrite <- ring_mul_assoc.
  rewrite (field_mul_comm F x (ring_add F x (ring_neg F a))).
  rewrite ring_mul_assoc.
  reflexivity.
Qed.
```

### `poly_remainder_core`
```coq
Lemma poly_remainder_core : forall (F : Field) (a x e q : ring_carrier F),
  ring_add F
    (ring_mul F (ring_add F x (ring_neg F a)) (ring_add F e (ring_mul F x q)))
    (ring_mul F a e)
  = ring_mul F x (ring_add F e (ring_mul F (ring_add F x (ring_neg F a)) q)).
```
`transitivity` + `poly_remainder_alg_A` + `poly_remainder_alg_B` で証明。

### `poly_remainder_theorem` (主定理)
```coq
Theorem poly_remainder_theorem :
  forall (F : Field) (f : list (ring_carrier F)) (a x : ring_carrier F),
    poly_eval F f x =
    ring_add F
      (ring_mul F (ring_add F x (ring_neg F a))
                  (poly_eval F (poly_synthetic_div F f a) x))
      (poly_eval F f a).
```
リスト帰納法（3ケース）で証明。

### `fp_remainder_theorem` (系)
`poly_remainder_theorem` を `znz_p_field p Hp` に適用。

## Proof Attempts & Diagnostics

### デバッグメモ: `ring_add_zero_r` の失敗
- `destruct cs` 後に Rocq が `poly_eval F [] x` を自動的に `ring_zero F` に iota-簡約するため、`rewrite poly_eval_nil` や `rewrite ring_add_zero_r` が「見つからない」エラーになる場合があった。
- **解決策**: singleton ケースには `cbn [poly_eval poly_synthetic_div]` を使って最初から完全展開し、`ring_add_zero_l` 1回で `reflexivity` に帰着させる。

## TODO
(すべて完了)
