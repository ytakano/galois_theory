# Proof Progress: znz_units_decomp（既約剰余類群の分解定理）

## Status Overview
- Overall: Complete
- Complete Lemmas: 8/8
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `znz_units_gcd_dvd`

```coq
Lemma znz_units_gcd_dvd : forall (m n : nat) (a : Z),
  Z.gcd a (Z.of_nat (m * n)) = 1 ->
  Z.gcd a (Z.of_nat m) = 1.
Proof.
  intros m n a H.
  apply Zis_gcd_gcd. lia.
  constructor.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros d Hda Hdm.
    assert (Hmn : Zis_gcd a (Z.of_nat (m * n)) 1).
    { rewrite <- H. apply Zgcd_is_gcd. }
    destruct Hmn as [_ _ H3].
    apply H3.
    + exact Hda.
    + rewrite Nat2Z.inj_mul. apply Z.divide_mul_r. exact Hdm.
Qed.
```

### `znz_units_gcd_mul`

```coq
Lemma znz_units_gcd_mul : forall (m n : nat) (a : Z),
  Z.gcd a (Z.of_nat m) = 1 ->
  Z.gcd a (Z.of_nat n) = 1 ->
  Z.gcd a (Z.of_nat (m * n)) = 1.
Proof.
  intros m n a Hm Hn.
  assert (Hrm : rel_prime a (Z.of_nat m)).
  { unfold rel_prime. rewrite <- Hm. apply Zgcd_is_gcd. }
  assert (Hrn : rel_prime a (Z.of_nat n)).
  { unfold rel_prime. rewrite <- Hn. apply Zgcd_is_gcd. }
  assert (Hr : rel_prime a (Z.of_nat m * Z.of_nat n)).
  { apply rel_prime_mult; assumption. }
  rewrite Nat2Z.inj_mul.
  apply Zis_gcd_gcd. lia.
  exact Hr.
Qed.
```

### `znz_units_coprime_mod_l/m/r`

```coq
Lemma znz_units_coprime_mod_l : forall (p q r : nat) (Hp : (0 < p)%nat) (a : Z),
  Z.gcd a (Z.of_nat (p * q * r)) = 1 ->
  Z.gcd (a mod Z.of_nat p) (Z.of_nat p) = 1.
(* rewrite <- znz_gcd_mod_eq; apply znz_units_gcd_dvd with (n := q*r); Nat.mul_assoc *)

Lemma znz_units_coprime_mod_m : forall (p q r : nat) (Hq : (0 < q)%nat) (a : Z),
  Z.gcd a (Z.of_nat (p * q * r)) = 1 ->
  Z.gcd (a mod Z.of_nat q) (Z.of_nat q) = 1.
(* rewrite <- znz_gcd_mod_eq; apply znz_units_gcd_dvd with (n := p*r); mul_comm/assoc *)

Lemma znz_units_coprime_mod_r : forall (p q r : nat) (Hr : (0 < r)%nat) (a : Z),
  Z.gcd a (Z.of_nat (p * q * r)) = 1 ->
  Z.gcd (a mod Z.of_nat r) (Z.of_nat r) = 1.
(* rewrite <- znz_gcd_mod_eq; apply znz_units_gcd_dvd with (n := p*q); mul_comm *)
```

### `znz_units_gcd_mul3`

```coq
Lemma znz_units_gcd_mul3 : forall (p q r : nat) (a : Z),
  Z.gcd a (Z.of_nat p) = 1 ->
  Z.gcd a (Z.of_nat q) = 1 ->
  Z.gcd a (Z.of_nat r) = 1 ->
  Z.gcd a (Z.of_nat (p * q * r)) = 1.
Proof.
  intros p q r a Hp Hq Hr.
  rewrite Nat.mul_assoc.
  apply znz_units_gcd_mul.
  - apply znz_units_gcd_mul; assumption.
  - exact Hr.
Qed.
```

### `znz_units_decomp_mul_mod`

```coq
Lemma znz_units_decomp_mul_mod : forall (p q r : nat) (Hp : (0 < p)%nat) (a b : Z),
  (a * b) mod Z.of_nat (p * q * r) mod Z.of_nat p =
  (a mod Z.of_nat p * (b mod Z.of_nat p)) mod Z.of_nat p.
Proof.
  intros p q r Hp a b.
  rewrite znz_mod_mod_l by exact Hp.
  apply Z.mul_mod. lia.
Qed.
```

### `Theorem znz_units_decomp`

```coq
Theorem znz_units_decomp :
  forall (p q r : nat) (Hp : (1 < p)%nat) (Hq : (1 < q)%nat) (Hr : (1 < r)%nat)
    (Hpqr : (1 < p * q * r)%nat),
    pairwise_coprime3 p q r ->
    znz_units_group (p * q * r) Hpqr ≅
    znz_units_group p Hp ×ₒ znz_units_group q Hq ×ₒ znz_units_group r Hr.
```
証明完了: 2026-04-04

## Proof Attempts & Diagnostics

### コメント内の (Z/nZ)* の記法について
- ⚠️ `(** ... (Z/nZ)*) *)` のように、Rocq コメント `(*..*)` の中に `*)` が含まれると構文エラー。
- 対処: `(Z/nZ)^*` と書くか、コメントを分割する。

### `Z.divide_mul_r` vs `Z.divide_mul_l` の方向
- `Z.divide_mul_r : (n | b) → (n | a * b)` — 右因子から積への拡張
- `Z.divide_mul_l : (n | a) → (n | a * b)` — 左因子から積への拡張
- ⚠️ 目標 `(d | Z.of_nat m * Z.of_nat n)` を `Hdm : (d | Z.of_nat m)`（左因子）から示すには `Z.divide_mul_l`。`Z.divide_mul_r` を使うと残りサブゴールが `(d | Z.of_nat n)` になり型不一致。

### `rewrite znz_gcd_mod_eq` の方向
- `znz_gcd_mod_eq : Z.gcd (a mod n) n = Z.gcd a n`
- LHS: `gcd(a mod n, n)` / RHS: `gcd(a, n)`
- 目標 `gcd(a mod p, p) = 1` を `gcd(a, p) = 1` に変換するには `rewrite znz_gcd_mod_eq`（LHS→RHS、`<-` なし）。
- 逆に目標 `gcd(a, p) = 1` を `gcd(a mod p, p) = 1` に変換するには `rewrite <- znz_gcd_mod_eq`（RHS→LHS）。

### `Nat.mul_assoc` の方向（Rocq 9.1）
- `Nat.mul_assoc : n * (m * p) = n * m * p`（LHS: 右括弧、RHS: 左結合）
- `rewrite Nat.mul_assoc` は LHS パターン `n * (m * p)` を探して `n * m * p` に変換
- `rewrite <- Nat.mul_assoc` は RHS パターン `n * m * p` を探して `n * (m * p)` に変換
- ⚠️ 目標が `(p * q) * r`（左結合形）の場合、`rewrite Nat.mul_assoc` は `a * (b * c)` を探すので見つからない。`rewrite <- Nat.mul_assoc` を使うか、直接 `apply` で回避する。

### `znz_units_decomp_mul_mod` の適用制限
- `znz_units_decomp_mul_mod (p q r : nat) ...` の結論は `mod Z.of_nat (p*q*r) mod Z.of_nat p`
- ⚠️ q 成分（`mod Z.of_nat q`）に apply すると Rocq が `q` を `p` に unify しようとして失敗
- 対処: このような汎用補題は `apply` せず、`znz_mod_mod_l/m/r` + `Z.mul_mod` を直接使う

### `ring` tactic と `nat`
- ⚠️ `replace ... by ring` は nat に対して "Cannot find a declared ring structure over 'nat'" エラーになる場合がある
- 対処: `Nat.mul_assoc`, `Nat.mul_comm` + `reflexivity` で明示的に書くか、`%nat` スコープをつける

## TODO
- (すべて完了)
