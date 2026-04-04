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

---

### `znz_decomp`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem znz_decomp :
    forall (p q r : nat) (Hp : (0 < p)%nat) (Hq : (0 < q)%nat) (Hr : (0 < r)%nat)
      (Hpqr : (0 < p * q * r)%nat),
      pairwise_coprime3 p q r ->
      znz_group (p * q * r) Hpqr ≅
      znz_group p Hp ×ₒ znz_group q Hq ×ₒ znz_group r Hr.
  ```
- **Proof Strategy**: `IsIsomorphism` の定義に従い `exists phi` で写像を与え、準同型性・単射性・全射性の3つを個別に証明する。写像は `φ([a]) = (([a mod p], [a mod q]), [a mod r])`。
- **Key Tactics**: `set phi`, `unfold IsIsomorphism`, `apply Z.mod_mod_divide`, `Zplus_mod`, `sig_eq`, `simpl`, `injection`, `apply Z.mod_divide`, `Zminus_mod`, `Zmod_0_l`, `crt_unique_3`, `crt_exists_3`
- **Dependencies**: `znz_dvd_mul3_l/m/r`, `znz_mod_mod_l/m/r`, `pairwise_coprime3`, `znz_group`, `group_product`, `sig_eq`, `crt_unique_3`, `crt_exists_3`, `Z.mod_mod_divide` (stdlib), `Zminus_mod` (stdlib), `Zmod_0_l` (stdlib)
- **Notes**:
  - ⚠️ Dead end: `Nat.mul_pos` は Rocq 9.1 では存在しない → `Hpqr : (0 < p*q*r)%nat` を引数として受け取る。
  - ⚠️ Dead end: `mod_mod_divide` (素の名前) は環境にない → `Z.mod_mod_divide` を使う。
  - ⚠️ Dead end: `apply sig_eq.` だけでは goal が `proj1_sig (exist _ a Ha) = ...` のまま → `apply sig_eq. simpl.` が必要。これがないと後続の `rewrite H1` が失敗する (「Found no subterm matching 'a mod Z.of_nat p'」エラー)。
  - ⚠️ Dead end: `Z.mod_0_l` は `a <> 0` が必要な版 → 無条件版 `Zmod_0_l` を使う。
  - `cong p a b` の証明: `apply Z.mod_divide. * lia. * rewrite Zminus_mod, Hi, Z.sub_diag. apply Zmod_0_l.` パターンが有効。
  - 全射性で `crt_exists_3` の境界型 `Z.of_nat p * Z.of_nat q * Z.of_nat r` を `znz_group` のキャリア境界 `Z.of_nat (p*q*r)` に変換するには `Nat2Z.inj_mul` を使う。
- **Date**: 2026-04-04

---

### `znz_units_group` (既約剰余類群)
- **Type**: Definition (Group)
- **Statement**:
  ```coq
  Definition znz_units_group (n : nat) (Hn : (1 < n)%nat) : Group.
  (* carrier: {x : Z | 0 <= x < Z.of_nat n /\ Z.gcd x (Z.of_nat n) = 1} *)
  (* op: [a] * [b] = [a*b mod n] *)
  ```
- **Proof Strategy**: 補助補題を順に証明し、最後に `refine {| ... |}` で群公理を埋める。
  1. `znz_gcd_one`: `Zis_gcd_gcd` + constructor で直接 Zis_gcd を構成
  2. `znz_gcd_mod_eq`: `Z.gcd_mod` (Rocq 9.1 形式) + `Z.gcd_comm`
  3. `znz_gcd_mul_coprime`: `rel_prime`, `rel_prime_mult`, `Zis_gcd_gcd`, `Zis_gcd_sym`
  4. `znz_coprime_bezout_inv`: `linear_diophantine` でベズー係数取得、`ring_simplify + lia` で合同証明
  5. `znz_units_inv_val`/`znz_units_inv_prop`: `epsilon` + `epsilon_spec` で逆元構成
  6. `znz_units_group`: `refine` + 各群公理
- **Key Tactics**: `Zis_gcd_gcd`, `Zgcd_is_gcd`, `Zis_gcd_sym`, `rel_prime_mult`, `rel_prime_sym`, `epsilon`, `epsilon_spec`, `Z.mod_add`, `Z.mod_small`, `Z.divide_add_r`, `Z.divide_mul_l`, `ring_simplify`, `lia`, `cbn [proj1_sig]`
- **Dependencies**: `linear_diophantine`, `znz_gcd_one`, `znz_gcd_mod_eq`, `znz_gcd_mul_coprime`, `znz_coprime_bezout_inv`, `sig_eq`, `Z.mod_pos_bound`, `Z.mod_small`, `Zmult_mod_idemp_l/r`, `Z.mul_assoc`
- **Notes**:
  - ⚠️ `Z.gcd_mod` の形式: Rocq 9.1 では `Z.gcd (a mod b) b = Z.gcd b a` (引数順注意)。正しい使い方: `rewrite Z.gcd_mod by lia; apply Z.gcd_comm`。
  - ⚠️ `linarith` は利用不可。`lia` で代替。
  - ⚠️ `assert (H : n | m)` の `|` は括弧必須: `assert (H : (n | m))`。
  - ⚠️ `cong_of_mod` / `mod_of_cong` / `cong_trans` は CRT セクション以降に定義。これより前では使えない。直接 `ring_simplify + lia` または `Z.mod_add + Z.mod_small` で代替。
  - ⚠️ `apply sig_eq; simpl` の後 `1 * a` が match 式に展開される場合は `cbn [proj1_sig]` を使い、`rewrite Z.mul_1_l` で `1 * a` を `a` に戻す。
  - ⚠️ `ltac:(lia)` を `refine` 内の term 位置で使うと conjunction ゴールに失敗することがある。事前に `assert` で証明しておくこと。
  - 逆元の存在証明: `epsilon_spec (inhabits 0%Z) P znz_coprime_bezout_inv` パターン。逆元公理: `unfold cong; destruct; Z.mod_add by lia; Z.mod_small`。
  - `rel_prime a n` への変換: `unfold rel_prime; apply Zis_gcd_sym; rewrite <- Ha; apply Zgcd_is_gcd` が定石。
- **Date**: 2026-04-04

---

### `znz_units_gcd_dvd`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma znz_units_gcd_dvd : forall (m n : nat) (a : Z),
    Z.gcd a (Z.of_nat (m * n)) = 1 ->
    Z.gcd a (Z.of_nat m) = 1.
  ```
: 1775132645:1;rocq compile  `Zis_gcd a m 1` に変換し `constructor` で3サブゴールを生成。第3サブゴールで `Zis_gcd a (m*n) 1` を `destruct` して第3フィールド H3 を取り出し、`Z.divide_mul_r` で d|m → d|m*n を示す。integer.v
- **Key Tactics**: `Zis_gcd_gcd`, `constructor`, `Z.divide_1_l`, `Zgcd_is_gcd`, `destruct Hmn as [_ _ H3]`, `Z.divide_mul_r`, `Nat2Z.inj_mul`
- **Dependencies**: `Zis_gcd_gcd`, `Zgcd_is_gcd`, `Z.divide_1_l`, `Z.divide_mul_r`, `Nat2Z.inj_mul`
- **Notes**: `destruct Hmn as [_ _ H3]` で Zis_gcd レコードの第3フィールドのみを取り出せる。
- **Date**: 2026-04-04

---

### `znz_units_gcd_mul`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma znz_units_gcd_mul : forall (m n : nat) (a : Z),
    Z.gcd a (Z.of_nat m) = 1 ->
    Z.gcd a (Z.of_nat n) = 1 ->
    Z.gcd a (Z.of_nat (m * n)) = 1.
  ```
- **Proof Strategy**: `unfold rel_prime; rewrite <- Hm; apply Zgcd_is_gcd` パターンで `rel_prime a (Z.of_nat m)` を得て、`rel_prime_mult` で `rel_prime a (Z.of_nat m * Z.of_nat n)` を構成。`Nat2Z.inj_mul` で `Z.of_nat (m*n)` に変換後 `Zis_gcd_gcd` で結論。
- **Key Tactics**: `unfold rel_prime`, `Zgcd_is_gcd`, `rel_prime_mult`, `Nat2Z.inj_mul`, `Zis_gcd_gcd`
- **Dependencies**: `rel_prime_mult`, `Zgcd_is_gcd`, `Zis_gcd_gcd`, `Nat2Z.inj_mul`
- **Notes**: `rel_prime_mult p q r : rel_prime p q → rel_prime p r → rel_prime p (q*r)` — 第1引数が固定。`rel_prime a m` から `a` が固定なので `rel_prime_mult a m n` がそのまま使える。
- **Date**: 2026-04-04

---

### `znz_units_coprime_mod_l/m/r`
- **Type**: Lemma (3個)
- **Statement**:
  ```coq
  Lemma znz_units_coprime_mod_l : forall (p q r : nat) (Hp : (0 < p)%nat) (a : Z),
    Z.gcd a (Z.of_nat (p * q * r)) = 1 ->
    Z.gcd (a mod Z.of_nat p) (Z.of_nat p) = 1.
  ```
- **Proof Strategy**: `znz_gcd_mod_eq` を逆向きに rewrite して `Z.gcd a (Z.of_nat p) = 1` に帰着し、`znz_units_gcd_dvd` で `Z.gcd a (Z.of_nat (p * (q*r))) = 1` から導く。`Nat.mul_assoc` で `p*q*r = p*(q*r)` に変形。
- **Key Tactics**: `rewrite <- znz_gcd_mod_eq`, `apply znz_units_gcd_dvd with (n := q*r)`, `Nat.mul_assoc`
- **Notes**: m版は `Nat.mul_comm` + `Nat.mul_assoc` で `q*(p*r)` に変形、r版は `Nat.mul_comm` で `r*(p*q)` に変形して `znz_units_gcd_dvd` を適用。
- **Date**: 2026-04-04

---

### `znz_units_gcd_mul3`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma znz_units_gcd_mul3 : forall (p q r : nat) (a : Z),
    Z.gcd a (Z.of_nat p) = 1 ->
    Z.gcd a (Z.of_nat q) = 1 ->
    Z.gcd a (Z.of_nat r) = 1 ->
    Z.gcd a (Z.of_nat (p * q * r)) = 1.
  ```
- **Proof Strategy**: `Nat.mul_assoc` で `p*q*r = (p*q)*r`、`znz_units_gcd_mul` を2回適用。
- **Key Tactics**: `Nat.mul_assoc`, `znz_units_gcd_mul`
- **Date**: 2026-04-04

---

### `znz_units_decomp_mul_mod`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma znz_units_decomp_mul_mod : forall (p q r : nat) (Hp : (0 < p)%nat) (a b : Z),
    (a * b) mod Z.of_nat (p * q * r) mod Z.of_nat p =
    (a mod Z.of_nat p * (b mod Z.of_nat p)) mod Z.of_nat p.
  ```
- **Proof Strategy**: `znz_mod_mod_l` で `mod (p*q*r) mod p = mod p`、`Z.mul_mod` で乗算分配則。
- **Key Tactics**: `znz_mod_mod_l`, `Z.mul_mod`, `lia`
- **Notes**: `Z.mul_mod` は ` 0` を必要とする。`lia` で `0 < p → Z.of_nat p ≠ 0` を処理。n 
- **Date**: 2026-04-04

---

### `znz_units_decomp`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem znz_units_decomp :
    forall (p q r : nat) (Hp : (1 < p)%nat) (Hq : (1 < q)%nat) (Hr : (1 < r)%nat)
      (Hpqr : (1 < p * q * r)%nat),
      pairwise_coprime3 p q r ->
      znz_units_group (p * q * r) Hpqr ≅
      znz_units_group p Hp ×ₒ znz_units_group q Hq ×ₒ znz_units_group r Hr.
  ```
- **Proof Strategy**: `znz_decomp`（加法群版）と同じ構造。写像 φ([a]) = (a mod p, a mod q, a mod r) を `set (phi := ...)` で定義し、準同型性・単射性・全射性の3つを個別に証明する。
  - 写像定義: carrier は `{x | range ∧ gcd=1}` の連言。`znz_units_coprime_mod_l/m/r` で各 gcd=1 を示す。
  - 準同型性: `znz_units_decomp_mul_mod` を各成分に適用。
  - 単射性: `injection Heq` → `crt_unique_3` → `sig_eq`（znz_decomp と同じ）。
  - 全射性: `crt_exists_3` で n 構成、`znz_gcd_mod_eq` + `znz_units_gcd_mul3` で `gcd(n,pqr)=1`。
- **Key Tactics**: `set phi`, `unfold IsIsomorphism`, `sig_eq`, `simpl`, `f_equal`, `znz_units_decomp_mul_mod`, `injection`, `crt_unique_3`, `Z.mod_divide`, `Zminus_mod`, `Zmod_0_l`, `crt_exists_3`, `znz_gcd_mod_eq`, `znz_units_gcd_mul3`
- **Dependencies**: `znz_units_coprime_mod_l/m/r`, `znz_units_gcd_mul3`, `znz_units_decomp_mul_mod`, `znz_units_group`, `group_product`, `pairwise_coprime3`, `crt_unique_3`, `crt_exists_3`, `sig_eq`, `Nat2Z.inj_mul`
- **Notes**:
  - ⚠️ コメント内に `(Z/nZ)*` と書くと `*)` がコメント閉じと解釈されて構文エラー。`(Z/nZ)^*` と書くこと。
  - carrier の型が `{x | range ∧ gcd=1}` の連言なので、`apply sig_eq; simpl` だけでなく、後続で `injection` を使う場合は連言の各成分が独立した H に分解される
  - 全射性での `proj2_sig` の構造: `proj2 (proj2_sig a)` が gcd 条件 `Z.gcd x n = 1` を取り出す。
- **Date**: 2026-04-04

---

## Pitfalls & Lessons Learned

### `Z.divide_mul_r` vs `Z.divide_mul_l`
- `Z.divide_mul_l : (n | a) → (n | a * b)` — left factor
- `Z.divide_mul_r : (n | b) → (n | a * b)` — right factor
- When goal is `(d | m * n)` and you have `(d | m)`, use `Z.divide_mul_l`.

### `rewrite znz_gcd_mod_eq` direction
- Forward (`rewrite`): converts `gcd(a mod n, n)` → `gcd(a, n)` in goal
- Backward (`rewrite <-`): converts `gcd(a, n)` → `gcd(a mod n, n)` in goal

### `Nat.mul_assoc` direction (Rocq 9.1)
- `Nat.mul_assoc : n * (m * p) = n * m * p` (LHS right-paren, RHS left-assoc)
 `n * m * p`
- Cannot use `rewrite` on a left-assoc goal; use direct `apply` with explicit args.

### `znz_units_decomp_mul_mod` unification issue
- Lemma conclusion's first `p` parameter causes unification failure for q/r components
- Fix: inline with `znz_mod_mod_l/m/r` + `Z.mul_mod` directly.

### `ring` tactic for `nat`
- May fail with "Cannot find a declared ring structure over 'nat'"
- Use `Nat.mul_assoc` + `Nat.mul_comm` + `reflexivity` for nat equalities instead.

### znz_units_group carrier conjunction
- carrier type is `{x | range /\ gcd = 1}` (conjunction)
- `crt_exists_3` expects just `range` bounds → use `proj1 Hx` not `Hx`
- gcd condition extraction: `proj2 Hx`

### `nat_gcd_mul_coprime`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma nat_gcd_mul_coprime : forall a b c : nat,
    Nat.gcd a c = 1%nat -> Nat.gcd b c = 1%nat -> Nat.gcd (a * b) c = 1%nat.
  ```
- **Proof Strategy**: Set d = gcd(a*b, c). Show gcd(d,a)=1 using gcd_greatest (d|d|c and gcd(d,a)|gcd(a,c)=1). Apply Nat.gauss to get d|b. Conclude d|gcd(b,c)=1.
- **Key Tactics**: `Nat.gcd_greatest`, `Nat.gauss`, `Nat.divide_trans`, `Nat.divide_1_r`
- **Dependencies**: Nat stdlib
- **Notes**: `Z_scope` must be open; use `1%nat` not `1` for the equality goals. `Nat.gauss` requires `n|(m*p)` where the divisor argument must be `(b*a)` form; use `destruct ... exists k; lia` to convert `Nat.divide d (a*b)` to `Nat.divide d (b*a)`.
- **Date**: 2026-04-14

### `euler_phi_three_prime_powers`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem euler_phi_three_prime_powers :
    forall (p q r e f g : nat),
      prime (Z.of_nat p) -> prime (Z.of_nat q) -> prime (Z.of_nat r) ->
      p <> q -> q <> r -> p <> r ->
      (1 <= e)%nat -> (1 <= f)%nat -> (1 <= g)%nat ->
      euler_phi (p ^ e * q ^ f * r ^ g) =
        (p ^ (e - 1) * (p - 1) * q ^ (f - 1) * (q - 1) * r ^ (g - 1) * (r - 1))%nat.
  ```
- **Proof Strategy**: Apply `euler_phi_mul` twice (using coprimality from `prime_pow_coprime_distinct` and `nat_gcd_mul_coprime`), then `euler_phi_prime_pow` three times, close with `nia`.
- **Key Tactics**: `Nat.pow_le_mono_r`, `nat_gcd_mul_coprime`, `euler_phi_mul`, `euler_phi_prime_pow`, `nia`
- **Dependencies**: `prime_pow_coprime_distinct` (Admitted), `count_multiples_in_range` (Admitted via euler_phi_prime_pow), `nat_gcd_mul_coprime`, `euler_phi_mul`, `euler_phi_prime_pow`
- **Notes**: ⚠️ `ring` does not work for nat (no ring structure declared); use `nia` instead. ⚠️ `Nat.one_lt_pow` doesn't exist; use `Nat.pow_le_mono_r` + `Nat.pow_1_r`. ⚠️ `Nat.Coprime.coprime_mul_l_iff` doesn't exist; prove `nat_gcd_mul_coprime` manually. ⚠️ `p^1` in Z scope parses as Z.pow; annotate `(p^1)%nat`. ⚠️ Do NOT use `rewrite <- Nat.mul_assoc` before `euler_phi_mul` as it changes the goal form.
- **Date**: 2026-04-14
