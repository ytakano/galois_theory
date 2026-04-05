# Proof Progress: fp_poly_roots_bound (Fp上のn次方程式の解はn個以下)

## Status Overview
- Overall: Complete
- Complete Lemmas: 10/10
- Unproven (`Admitted`): なし
- Failed/Abandoned Items: なし

## Completed Lemmas

### `ring_sub_zero_iff_eq`
```coq
Lemma ring_sub_zero_iff_eq : forall (R : Ring) (a b : ring_carrier R),
  ring_add R a (ring_neg R b) = ring_zero R <-> a = b.
Proof.
  intros R a b.
  split.
  - intros H.
    assert (H2 : ring_add R (ring_add R a (ring_neg R b)) b =
                 ring_add R (ring_zero R) b).
    { rewrite H. reflexivity. }
    rewrite ring_add_assoc in H2.
    rewrite ring_add_neg_l in H2.
    rewrite ring_add_zero_r in H2.
    rewrite ring_add_zero_l in H2.
    exact H2.
  - intros H. subst. apply ring_add_neg_r.
Qed.
```

### `poly_eval_single`
```coq
Lemma poly_eval_single : forall (F : Field) (c x : ring_carrier F),
  poly_eval F [c] x = c.
Proof.
  intros F c x.
  rewrite poly_eval_cons. rewrite poly_eval_nil.
  rewrite ring_mul_zero_r. apply ring_add_zero_r.
Qed.
```

### `poly_synthetic_div_length`
```coq
Lemma poly_synthetic_div_length :
  forall (F : Field) (c : ring_carrier F) (cs : list (ring_carrier F))
         (a : ring_carrier F),
    length (poly_synthetic_div F (c :: cs) a) = length cs.
Proof.
  intros F c cs a.
  induction cs as [| c' cs' IH].
  - reflexivity.
  - rewrite poly_synthetic_div_cons.
    change (S (length (poly_synthetic_div F (c' :: cs') a)) = S (length cs')).
    f_equal. exact IH.
Qed.
```

### `last_cons_nonempty`
```coq
Lemma last_cons_nonempty :
  forall (A : Type) (h : A) (t : list A) (d : A),
    t <> [] -> last (h :: t) d = last t d.
Proof.
  intros A h t d Ht. destruct t.
  - contradiction.
  - reflexivity.
Qed.
```

### `poly_synthetic_div_last`
```coq
Lemma poly_synthetic_div_last :
  forall (F : Field) (f : list (ring_carrier F)) (a d : ring_carrier F),
    (2 <= length f)%nat ->
    last (poly_synthetic_div F f a) d = last f d.
(* 証明: induction on f, base cases by intro Hlen; simpl in Hlen; lia,
         length=2 case by poly_eval_single,
         length≥3 case by last_cons_nonempty + IH *)
```

### `poly_nonzero_leading` (定義)
```coq
Definition poly_nonzero_leading (F : Field) (f : list (ring_carrier F)) : Prop :=
  f <> [] /\ last f (ring_zero F) <> ring_zero F.
```

### `poly_nonzero_leading_div`
```coq
Lemma poly_nonzero_leading_div :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_nonzero_leading F f -> (2 <= length f)%nat ->
    poly_nonzero_leading F (poly_synthetic_div F f a).
(* poly_synthetic_div_length + poly_synthetic_div_last で証明 *)
```

### `poly_const_nonzero_no_root`
```coq
Lemma poly_const_nonzero_no_root :
  forall (F : Field) (c x : ring_carrier F),
    c <> ring_zero F -> poly_eval F [c] x <> ring_zero F.
Proof.
  intros F c x Hc. rewrite poly_eval_single. exact Hc.
Qed.
```

### `poly_div_root`
```coq
Lemma poly_div_root :
  forall (F : Field) (f : list (ring_carrier F)) (a b : ring_carrier F),
    poly_eval F f a = ring_zero F -> poly_eval F f b = ring_zero F ->
    b <> a -> poly_eval F (poly_synthetic_div F f a) b = ring_zero F.
(* poly_remainder_theorem + ring_sub_zero_iff_eq + field_no_zero_divisors *)
```

### `poly_roots_bound` (主定理)
```coq
Theorem poly_roots_bound :
  forall (F : Field) (f : list (ring_carrier F)),
    poly_nonzero_leading F f ->
    forall (roots : list (ring_carrier F)),
      NoDup roots ->
      (forall a, In a roots -> poly_eval F f a = ring_zero F) ->
      (length roots < length f)%nat.
(* length f の ≤ 版強帰納法。因数定理 + poly_div_root + poly_nonzero_leading_div *)
```

### `fp_poly_roots_bound` (系)
```coq
Corollary fp_poly_roots_bound :
  forall (p : nat) (Hp : prime (Z.of_nat p))
         (f : list (ring_carrier (znz_p_field p Hp))),
    poly_nonzero_leading (znz_p_field p Hp) f ->
    forall (roots : list (ring_carrier (znz_p_field p Hp))),
      NoDup roots ->
      (forall a, In a roots ->
        poly_eval (znz_p_field p Hp) f a = ring_zero (znz_p_field p Hp)) ->
      (length roots < length f)%nat.
(* poly_roots_bound の直接適用 *)
```

## Proof Attempts & Diagnostics

### トラブルシューティング記録

1. **`poly_synthetic_div_length` の Z スコープ問題**:
   - `length f - 1` が Z スコープで Z 減算として解釈された。
   - 対策: 補題の形式を `length (poly_synthetic_div F (c :: cs) a) = length cs` に変更して減算を排除。

2. **`simpl length` が poly_synthetic_div を展開する問題**:
   - `simpl` は transparent な Fixpoint を展開するため `length (poly_synthetic_div ...)` を完全展開してしまう。
   - 対策: `change` タクティクで定義等値を明示的に使用。

3. **`omega` が使用不可**:
   - このファイルは `omega` をインポートしていない（`lia` のみ）。
   - 対策: 全 `omega` を `lia` に置換。

4. **`poly_roots_bound` 末尾の `lia` 失敗**:
   - `simpl` がゴールの `length` を展開するが仮説 `Hlq` は展開しないため不一致。
   - 対策: `rewrite Hlq in Hlen_rest; simpl length in Hlen_rest; simpl length; lia`。

## TODO
(すべて完了)

