# Proof Knowledge Base

このファイルは `rocq-prover` スキルが自動的に管理する、証明済み補題・定理の知識ベースです。
新しい証明セッションを始める前に必ずこのファイルを読み込んでください。

---

## Lemmas and Theorems

### `op_cancel_l`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma op_cancel_l : forall (G : Group) (x y z : carrier G),
    op G x y = op G x z -> y = z.
  ```
- **Proof Strategy**: 両辺の左から `inv G x` を掛ける。結合律・左逆元・左単位元を順に適用して `y = z` を導く。
- **Key Tactics**: `intros`, `apply`, `rewrite`, `left_inv`, `left_id`, `assoc`
- **Dependencies**: Group axioms (`assoc`, `left_inv`, `left_id`)
- **Notes**: `equal_powers_imply_period` の核心部分で使用する。`Open Scope Z_scope` 下では自然数の不等式に `%nat` が必要。
- **Date**: 2026-04-03

---

### `equal_powers_imply_period`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma equal_powers_imply_period :
    forall (G : Group) (a : carrier G) (i j : nat),
      (i < j)%nat ->
      gpow G a (Z.of_nat i) = gpow G a (Z.of_nat j) ->
      gpow G a (Z.of_nat (j - i)) = e G.
  ```
- **Proof Strategy**: 両辺の左から `gpow G a (Z.of_nat i)` の逆元を掛ける。`gpow_add` で `g^(j-i) = g^j / g^i = e`。
- **Key Tactics**: `intros`, `apply op_cancel_l`, `rewrite gpow_add`, `rewrite gpow_nat_inv_eq`, `lia`
- **Dependencies**: `op_cancel_l`, `gpow_add`, `gpow_nat_inv_eq`, `gpow_nat_comm`
- **Notes**: `(i < j)%nat` と `%nat` スコープ明示が必要。`Z.of_nat (j - i)` の等式は `lia` / `omega` で処理できる部分がある。
- **Date**: 2026-04-03

---

### `pigeonhole_Fin`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma pigeonhole_Fin :
    forall (m : nat) (h : nat -> Fin.t m),
      exists i j : nat,
        i < j /\ j <= m /\ h i = h j.
  ```
- **Proof Strategy**: `h 0, h 1, ..., h m` は `m+1` 個の値を `Fin.t m`（m 要素）に送るため重複が必至。`Fin.eq_dec` による決定的等号と `List.NoDup` の矛盾から導く。`fin_all` リストを構築して `NoDup` を仮定し、長さの矛盾を `fin_all_NoDup`, `fin_all_length` で導く。
- **Key Tactics**: `induction`, `destruct`, `Fin.eq_dec`, `List.NoDup`, `List.In`, `omega`
- **Dependencies**: `fin_all_length`, `fin_all_complete`, `fin_all_NoDup`, `not_NoDup_has_dup`, `Fin_injective_le`
- **Notes**: Rocq で素朴に書くと証明が重くなる。`Fin.t` の帰納的構造と `List.NoDup` の組み合わせが鍵。
- **Date**: 2026-04-03

---

### `pigeonhole_powers`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma pigeonhole_powers :
    forall (C : CyclicGroup) (m : nat)
      (f : carrier C -> Fin.t m),
      (forall x y, f x = f y -> x = y) ->
      exists i j : nat,
        i < j /\ j <= m /\
        gpow C (generator C) (Z.of_nat i)
        = gpow C (generator C) (Z.of_nat j).
  ```
- **Proof Strategy**: `h k := f (gpow C (generator C) (Z.of_nat k))` を定義し、`pigeonhole_Fin` を適用。`f` の単射性から `g^i = g^j` を導く。
- **Key Tactics**: `apply pigeonhole_Fin`, `intros`, `exists`, `split`, `apply (H _ _)`
- **Dependencies**: `pigeonhole_Fin`
- **Notes**: `GroupOrder C m` の全単射性から単射 `f` を取り出すステップが必要。`f` の単射性の仮定は `forall x y, f x = f y -> x = y` として渡す。
- **Date**: 2026-04-03

---

### `gpow_reduce_mod`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma gpow_reduce_mod :
    forall (G : Group) (a : carrier G) (d : nat) (z : Z),
      gpow G a (Z.of_nat d) = e G ->
      0 < d ->
      gpow G a z = gpow G a (z mod Z.of_nat d).
  ```
- **Proof Strategy**: `z = (z / d) * d + (z mod d)` の分解（`Z.div_mod`）を使い、`gpow_add` と `gpow_mul` で `g^((z/d)*d) = (g^d)^(z/d) = e^(z/d) = e` を適用。
- **Key Tactics**: `rewrite Z.div_mod`, `rewrite gpow_add`, `rewrite gpow_mul`, `rewrite H`, `rewrite gpow_nat_e`, `left_id`
- **Dependencies**: `gpow_add`, `gpow_mul`, `gpow_nat_e`, `Z.div_mod`
- **Notes**: `Z.div_mod` は `d ≠ 0` を必要とする。`Z.of_nat d ≠ 0` は `omega` / `lia` で処理。
- **Date**: 2026-04-03

---

### `cyclic_group_order_le_period`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma cyclic_group_order_le_period :
    forall (C : CyclicGroup) (m d : nat),
      GroupOrder C m ->
      0 < d ->
      gpow C (generator C) (Z.of_nat d) = e C ->
      m <= d.
  ```
- **Proof Strategy**: 任意の `x : carrier C` に `cyclic_property` より `x = g^z`。`z = q*d + r` (0 ≤ r < d) に分解し `g^z = g^r`。よって全元が `{g^0, ..., g^(d-1)}` に入る（高々 d 個）。`GroupOrder C m` の全単射性と合わせて `m ≤ d`。
- **Key Tactics**: `destruct (cyclic_property C x)`, `rewrite gpow_reduce_mod`, `Z.mod_pos_bound`, `apply Fin.bijection_le`
- **Dependencies**: `gpow_reduce_mod`, `cyclic_property`, `GroupOrder`, `gpow_add`, `gpow_mul`
- **Notes**: `Z.mod_pos_bound` で `0 ≤ r < d` を得る。有限集合への単射から `m ≤ d` を導く部分は `Fin` の性質（単射 `Fin.t m → Fin.t d` が存在 → `m ≤ d`）を使う。
- **Date**: 2026-04-03

---

### `generator_order`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma generator_order : forall (C : CyclicGroup) (m : nat),
    GroupOrder C m ->
    gpow C (generator C) (Z.of_nat m) = e C.
  ```
- **Proof Strategy**:
  1. `GroupOrder C m` から単射 `f : carrier C → Fin.t m` を取り出す
  2. `pigeonhole_powers f` で `i < j ≤ m`, `g^i = g^j` を得る
  3. `equal_powers_imply_period` で `d := j - i`, `g^d = e`, `0 < d ≤ m`
  4. `cyclic_group_order_le_period` で `m ≤ d`
  5. `d ≤ m` かつ `m ≤ d` → `d = m` → `g^m = e`
- **Key Tactics**: `destruct (GroupOrder)`, `apply pigeonhole_powers`, `apply equal_powers_imply_period`, `apply cyclic_group_order_le_period`, `omega`/`lia`
- **Dependencies**: `pigeonhole_powers`, `equal_powers_imply_period`, `cyclic_group_order_le_period`, `GroupOrder`
- **Notes**: `d = m` の等式は `omega` / `lia` で処理。`Z.of_nat (j - i) = Z.of_nat j - Z.of_nat i` には `Nat2Z.inj_sub` が必要な場合がある。
- **Date**: 2026-04-03

---

### `fin_all_length` / `fin_all_complete` / `fin_all_NoDup`
- **Type**: Lemma (3つの補題)
- **Statement**:
  ```coq
  (* fin_all n は Fin.t n の全要素リスト *)
  Lemma fin_all_length : forall n, length (fin_all n) = n.
  Lemma fin_all_complete : forall n (x : Fin.t n), In x (fin_all n).
  Lemma fin_all_NoDup : forall n, NoDup (fin_all n).
  ```
- **Proof Strategy**: `fin_all` を `Fin.t` の帰納的構造に基づいて再帰的に定義し、各性質を帰納法で証明。
- **Key Tactics**: `induction n`, `simpl`, `constructor`, `apply in_map`, `apply NoDup_map`
- **Dependencies**: `Fin.t` の帰納的定義、`List.NoDup`、`List.In`
- **Notes**: `fin_all` の定義自体が補題の証明の鍵。`Fin.F1` と `Fin.FS` で場合分け。
- **Date**: 2026-04-03

---

### `not_NoDup_has_dup`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma not_NoDup_has_dup :
    forall {A} (l : list A),
      ~NoDup l ->
      exists i j, i < j < length l /\ nth_error l i = nth_error l j.
  ```
- **Proof Strategy**: `NoDup` の否定から重複要素の存在を導く。帰納法と `In` を組み合わせる。
- **Key Tactics**: `induction l`, `destruct`, `apply Classical_Prop.not_and_or`
- **Dependencies**: `List.NoDup`, `List.nth_error`
- **Notes**: 古典論理（`Classical_Prop`）が必要な場合がある。
- **Date**: 2026-04-03

---

### `Fin_injective_le`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma Fin_injective_le :
    forall m n (f : Fin.t m -> Fin.t n),
      (forall x y, f x = f y -> x = y) ->
      m <= n.
  ```
- **Proof Strategy**: `fin_all m` の各要素を `f` で写した像リストが `NoDup` で長さ `m` → `Fin.t n` に `m` 個の異なる要素 → `m ≤ n`。
- **Key Tactics**: `apply NoDup_map_inj`, `apply fin_all_NoDup`, `rewrite fin_all_length`, `apply NoDup_incl_length`
- **Dependencies**: `fin_all_length`, `fin_all_NoDup`, `List.NoDup_map`
- **Notes**: `NoDup_incl_length` か同等の補題（`List` ライブラリ）が必要。
- **Date**: 2026-04-03
