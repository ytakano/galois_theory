# Proof Progress: znz_decomp

## Status Overview
- Overall: Complete
- Complete Lemmas: 7/7
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `znz_dvd_mul3_l`, `znz_dvd_mul3_m`, `znz_dvd_mul3_r`

```coq
Lemma znz_dvd_mul3_l : forall (p q r : nat),
  (Z.of_nat p | Z.of_nat (p * q * r)).
Proof.
  intros p q r.
  rewrite Nat2Z.inj_mul, Nat2Z.inj_mul.
  exists (Z.of_nat q * Z.of_nat r). ring.
Qed.
(* m, r 版も同様 *)
```

### `znz_mod_mod_l`, `znz_mod_mod_m`, `znz_mod_mod_r`

```coq
Lemma znz_mod_mod_l : forall (p q r : nat) (a : Z),
  (0 < p)%nat ->
  (a mod Z.of_nat (p * q * r)) mod Z.of_nat p = a mod Z.of_nat p.
Proof.
  intros p q r a Hp.
  apply Z.mod_mod_divide.
  apply znz_dvd_mul3_l.
Qed.
(* m, r 版も同様 *)
```

- `Z.mod_mod_divide` は `Z.` プレフィックスが必要 (`mod_mod_divide` (素の名前) は環境に存在しない)。

### `Theorem znz_decomp`

```coq
Theorem znz_decomp :
  forall (p q r : nat) (Hp : (0 < p)%nat) (Hq : (0 < q)%nat) (Hr : (0 < r)%nat)
    (Hpqr : (0 < p * q * r)%nat),
    pairwise_coprime3 p q r ->
    znz_group (p * q * r) Hpqr ≅
    znz_group p Hp ×ₒ znz_group q Hq ×ₒ znz_group r Hr.
```

証明完了: 2026-04-04

#### 主要な落とし穴まとめ

1. **`Nat.mul_pos` が存在しない**: `(0 < p * q * r)` の証明を定理シグネチャの引数 `Hpqr` として受け取るよう変更。
2. **`mod_mod_divide` → `Z.mod_mod_divide`**: stdlib の名前は `Z.` プレフィックスが必要。
3. **`injection Heq` 後の型**: `apply sig_eq. simpl.` が必要。`simpl` がないと `proj1_sig (exist _ a Ha)` が `a` に簡約されず、後続の `rewrite H1` が失敗する。
4. **`Z.mod_0_l` は引数 `<> 0` が必要**: `Zmod_0_l`（無条件版）を使う。
5. **`cong` の証明**: `apply Z.mod_divide.` の後、`Zminus_mod`, `rewrite Hi`, `Z.sub_diag`, `Zmod_0_l` のチェーンで `(a - b) mod p = 0` を示す。
6. **単射性の `cong` サブゴール**: `apply crt_unique_3` の前に `simpl.` (from `apply sig_eq. simpl.`) で `n1, n2` を `a, b` に unify する。
7. **全射性の境界変換**: `crt_exists_3` は `Z.of_nat p * Z.of_nat q * Z.of_nat r` 形式の境界を返すが、`znz_group (p*q*r)` のキャリアは `Z.of_nat (p*q*r)` 形式。`Nat2Z.inj_mul` で変換。

## TODO
- (すべて完了)
