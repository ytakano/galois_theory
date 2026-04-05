# Proof Plan: znz_p_field (Z/pZ は素数 p のとき体)

## Goal

素数 p に対して `znz_p_field (p : nat) (Hp : prime (Z.of_nat p)) : Field` を完全に証明する。

## 現状の問題

前回 `Admitted` にした原因:
- `field_inv : ring_carrier field_ring → ring_carrier field_ring` に型不整合
- `ring_carrier = Z` を使うと `ring_add_zero_l : 0 + a = a` が `Z` 全体では成立しない（`a mod p ≠ a` となる場合がある）
- `znz_units_inv_val` の引数型は `{x : Z | 0 <= x < p /\ gcd(x,p)=1}` で、`Z` や `{x | 0<=x<p}` とは異なる

## 設計方針

`ring_carrier := {x : Z | 0 <= x < Z.of_nat p}` (sigma 型、`znz_group` と同じ) を採用する。

- 加法は `znz_group` と完全に同じ
- 乗法を追加: `fun a b => exist _ ((proj1_sig a * proj1_sig b) mod p) (...)`
- 乗法単位元: `exist _ (1 mod p) (...)`
- `field_inv`: 新しい helper で定義

## 補助定義・補題の設計

### Step 1: `znz_field_inv_val` (補助定義)

```coq
Definition znz_field_inv_val (p : nat)
    (a : {x : Z | 0 <= x < Z.of_nat p}) : Z :=
  epsilon (inhabits 0%Z)
    (fun b => 0 <= b < Z.of_nat p /\ cong p (proj1_sig a * b) 1).
```

`znz_units_inv_val` と同構造だが、引数の型を `{x | 0<=x<p}` (gcd 条件なし) にする。

### Step 2: `znz_field_inv_spec` (補助補題)

```coq
Lemma znz_field_inv_spec : forall (p : nat) (Hp : prime (Z.of_nat p))
    (a : {x : Z | 0 <= x < Z.of_nat p}),
  proj1_sig a <> 0 ->
  0 <= znz_field_inv_val p a < Z.of_nat p /\
  cong p (proj1_sig a * znz_field_inv_val p a) 1.
```

**証明方針**:
1. `proj1_sig a ≠ 0` と `0 <= proj1_sig a < p` (sigma 型から) を合わせると `0 < proj1_sig a < p`
2. `Z.mod_small` より `proj1_sig a mod p = proj1_sig a`、よって `≠ 0`
3. `znz_prime_nonzero_coprime` → `Z.gcd (proj1_sig a) (Z.of_nat p) = 1`
4. `znz_coprime_bezout_inv` → `∃ b, 0 <= b < p /\ cong p (proj1_sig a * b) 1`
5. `epsilon_spec` → `znz_field_inv_val p a` が上記条件を満たす

### Step 3: `znz_p_field` 本体

**carrier**: `{x : Z | 0 <= x < Z.of_nat p}`

**ring フィールド**:
| フィールド | 値 | 証明 |
|---|---|---|
| `ring_carrier` | `{x : Z | 0 <= x < Z.of_nat p}` | — |
| `ring_add` | `exist _ ((a + b) mod p) (mod_pos_bound)` | znz_group と同じ |
| `ring_zero` | `exist _ 0 (conj le_refl HN)` | znz_group と同じ |
| `ring_neg` | `exist _ ((-a) mod p) (mod_pos_bound)` | znz_group と同じ |
| `ring_mul` | `exist _ ((a * b) mod p) (mod_pos_bound)` | znz_units_group と同じパターン |
| `ring_one` | `exist _ (1 mod p) (mod_pos_bound)` | znz_units_group の e と同様 |

**Ring 公理の証明** (すべて `sig_eq` + Z 算術):
| 公理 | 使うキー補題 |
|---|---|
| `ring_add_assoc` | `Zplus_mod_idemp_l/r`, `Z.add_assoc` |
| `ring_add_comm` | `Z.add_comm` |
| `ring_add_zero_l` | `Z.mod_small` (sigma 型の範囲条件を使う) |
| `ring_add_neg_l` | `Zplus_mod_idemp_l`, `Z.add_opp_diag_l`, `Zmod_0_l` |
| `ring_mul_assoc` | `Zmult_mod_idemp_l/r`, `Z.mul_assoc` |
| `ring_mul_one_l` | `Zmult_mod_idemp_r`, `Z.mul_1_l`, `Z.mod_small` |
| `ring_mul_one_r` | `Zmult_mod_idemp_l`, `Z.mul_1_r`, `Z.mod_small` |
| `ring_distr_l` | `Zmult_mod_idemp_r`, `Zplus_mod_idemp_l/r`, `Z.mul_add_distr_l` |
| `ring_distr_r` | `Zmult_mod_idemp_l`, `Zplus_mod_idemp_l/r`, `Z.mul_add_distr_r` |

**Field フィールドの証明**:

#### `field_inv`:
```
intro a.
destruct (Z.eq_dec (proj1_sig a) 0) as [Ha0 | Ha0].
- (* a = 0 の場合: 0 を返す (field_inv_l では使われない) *)
  exact (exist _ 0 (conj (Z.le_refl 0) HN)).
- (* a ≠ 0 の場合: znz_field_inv_val の値 *)
  exact (exist _ (znz_field_inv_val p a)
           (proj1 (znz_field_inv_spec p Hp a Ha0))).
```

#### `field_mul_comm`:
```
intros [a Ha] [b Hb]. apply sig_eq. simpl.
rewrite Zmult_mod_idemp_r, Zmult_mod_idemp_l, Z.mul_comm. reflexivity.
```
(または単に `Z.mul_comm` + idemp 補題)

#### `field_inv_l`:
```
intros x Hx.
(* x ≠ ring_zero → proj1_sig x ≠ 0 *)
assert (Ha : proj1_sig x ≠ 0).
{ intro Heq. apply Hx. apply sig_eq. simpl. exact Heq. }
(* field_inv F x は znz_field_inv_val ブランチ *)
(* ring_mul F (field_inv F x) x = exist _ ((inv_val * proj1_sig x) mod p) ... *)
apply sig_eq. simpl.
(* (znz_field_inv_val p x * proj1_sig x) mod p = 1 mod p *)
destruct (znz_field_inv_spec p Hp x Ha) as [_ Hcong].
(* Hcong : cong p (proj1_sig x * znz_field_inv_val p x) 1 *)
rewrite Z.mul_comm.
unfold cong in Hcong. destruct Hcong as [k Hk].
assert (Heq : proj1_sig x * znz_field_inv_val p x = Z.of_nat p * k + 1) by lia.
rewrite Heq.
replace (Z.of_nat p * k + 1) with (1 + k * Z.of_nat p) by ring.
rewrite Z.mod_add by lia.
apply Z.mod_small. lia.
```

#### `field_one_ne_zero`:
```
intro Heq.
(* ring_one = exist _ (1 mod p) ..., ring_zero = exist _ 0 ... *)
(* sig_eq → 1 mod p = 0 → 矛盾 (p ≥ 2) *)
apply (f_equal proj1_sig) in Heq.
simpl in Heq.
rewrite Z.mod_small in Heq by lia.
lia.
```

## 実装順序

1. `znz_field_inv_val` の定義
2. `znz_field_inv_spec` の証明
3. `znz_p_field` の定義・証明 (`Admitted` を置き換え)

## 注意事項

- `sig_eq` は `apply sig_eq. simpl.` の順で使う (先に `sig_eq` してから simpl で proj1_sig を展開)
- `ring_mul_one_l/r` では `znz_units_group` の同様の証明を参照する (line 2026-2034)
- `field_inv` は `Z.eq_dec` で場合分け → `field_inv_l` の証明では `destruct Z.eq_dec` して `Ha0 : proj1_sig x ≠ 0` の場合だけ考える
- `cong p a b := (Z.of_nat p | a - b)`、変換は `lia` で `a - b = p * k → a = p * k + b` の形にする

