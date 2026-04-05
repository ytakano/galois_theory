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

### `mod_add_mul_small`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma mod_add_mul_small : forall p r m : nat,
    (0 < p)%nat -> (r < p)%nat -> ((p * m + r) mod p = r)%nat.
  ```
- **Proof Strategy**: `Nat.mul_comm + Nat.add_comm` to rewrite to `(r + m * p) mod p`, then `Nat.Div0.mod_add` to get `r mod p`, then `Nat.mod_small`.
- **Key Tactics**: `rewrite Nat.mul_comm, Nat.add_comm`, `rewrite Nat.Div0.mod_add`, `apply Nat.mod_small`
- **Dependencies**: `Nat.Div0.mod_add`, `Nat.mod_small`
- **Notes**: `Nat.Div0.mod_add : (a + b * c) mod c = a mod c`. The `Div0` variant avoids divisibility side conditions.
- **Date**: 2026-04-15

### `filter_false_forall`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma filter_false_forall :
    forall (A : Type) (f : A -> bool) (l : list A),
      List.Forall (fun x => f x = false) l ->
      List.filter f l = [].
  ```
- **Proof Strategy**: Induction on the Forall proof; unfold one filter step with `cbn [List.filter]`.
- **Key Tactics**: `induction H`, `cbn [List.filter]`, `rewrite Hx`
- **Dependencies**: none
- **Notes**: `simpl` on `List.filter` may unfold arithmetic inside predicates; use `cbn [List.filter]` instead to unfold only the filter step.
- **Date**: 2026-04-15

### `filter_window_single_multiple`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma filter_window_single_multiple :
    forall (p m : nat),
      (0 < p)%nat ->
      List.filter (fun k => Nat.eqb (Nat.modulo k p) 0) (List.seq (p * m) p) = [(p * m)%nat].
  ```
- **Proof Strategy**: `destruct p as [| p']`. In Z_scope, annotate the singleton list as `[(p * m)%nat]`. Use `cbn [List.seq]; cbn [List.filter]` to expose head element. Prove head passes with `Nat.mul_comm + Nat.Div0.mod_mul`. Prove tail is filtered out via `filter_false_forall + Forall_forall + in_seq + mod_add_mul_small`.
- **Key Tactics**: `destruct p as [| p']`, `cbn [List.seq]`, `cbn [List.filter]`, `Nat.eqb_eq`, `Nat.Div0.mod_mul`, `filter_false_forall`, `List.Forall_forall`, `List.in_seq`
- **Dependencies**: `mod_add_mul_small`, `filter_false_forall`
- **Notes**: ⚠️ `change (S p') with (1 + p') at 3` fails in Z_scope. ⚠️ `simpl` expands Nat.modulo into divmod form; use `cbn [List.filter]` instead. ⚠️ Do NOT use `simpl in Hhi` after `in_seq` destructuring — this unfolds multiplication making `lia` unable to reason. ⚠️ `assert (Hk_eq : k = S p' * m + (k - S p' * m)) by lia` needs `%nat` annotation in Z_scope. ⚠️ The result list `[p * m]` must be annotated `[(p * m)%nat]` in Z_scope.
- **Date**: 2026-04-15

### `count_multiples_in_range`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma count_multiples_in_range :
    forall (p m : nat),
      (0 < p)%nat ->
      List.length (List.filter (fun k => Nat.eqb (k mod p) 0) (List.seq 0 (p * m))) = m.
  ```
- **Proof Strategy**: Induction on m. Base: `rewrite Nat.mul_0_r`. Step: split `seq 0 (p*(m'+1))` = `seq 0 (p*m') ++ seq (p*m') p` via `List.seq_app`; apply `filter_window_single_multiple` for the window; combine with IH via `app_length`.
- **Key Tactics**: `induction m`, `Nat.mul_0_r`, `List.seq_app`, `List.filter_app`, `List.app_length`, `filter_window_single_multiple`
- **Dependencies**: `filter_window_single_multiple`
- **Notes**: `rewrite Nat.mul_0_r` needed for base case (not `simpl`). Use `replace (p * S m') with (p * m' + p) by lia` to expose the split point. `replace (0 + p * m') with (p * m') by lia` to normalize seq start.
- **Date**: 2026-04-15

### `prime_pow_coprime_distinct`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma prime_pow_coprime_distinct :
    forall (p q e f : nat),
      prime (Z.of_nat p) ->
      prime (Z.of_nat q) ->
      p <> q ->
      Nat.gcd (p ^ e) (q ^ f) = 1%nat.
  ```
- **Proof Strategy**: 3 steps: (1) `Z.gcd(p,q) = 1` via `prime_divisors + prime_ge_2` to show `¬(p|q)`, then `prime_rel_prime + Zis_gcd_gcd`; (2) extend to powers via `Nat2Z.inj_pow + Z.coprime_pow_l + Z.coprime_pow_r`; (3) convert Nat.gcd to 1 via `Z.gcd_greatest + Z.divide_1_r + Nat2Z.inj`.
- **Key Tactics**: `prime_divisors`, `prime_ge_2`, `prime_rel_prime`, `Zis_gcd_gcd`, `Nat2Z.inj_pow`, `Z.coprime_pow_l`, `Z.coprime_pow_r`, `Z.gcd_greatest`, `Z.divide_1_r`, `Nat2Z.inj`
- **Dependencies**: `Znumtheory`, `Zdivisibility`, `Nat2Z`
- **Notes**: ⚠️ `integer.v` uses old `prime` (not `Z.prime`), so use `prime_rel_prime/prime_ge_2/prime_divisors` not their `Z.*` replacements. ⚠️ `Nat2Z.inj_1` doesn't exist; use `simpl` after `apply Nat2Z.inj` to reduce `Z.of_nat 1`. ⚠️ `Z.divide_1_r : (n|1) → n=1 ∨ n=-1`; case split and use `Nat2Z.is_nonneg` + `lia` to eliminate `n=-1`. ⚠️ `Nat.gcd_divide_l/r` returns `Nat.divide` (∃ k, n = k*d), not `∃ k, n = d*k`; use `lia` to flip: `rewrite <- Nat2Z.inj_mul; f_equal; lia`.
- **Date**: 2026-04-15

---

### `Ring` Record
- **Type**: Record (定義)
- **Statement**:
  ```coq
  Record Ring : Type := {
    ring_carrier : Type;
    ring_add / ring_zero / ring_neg / ring_mul / ring_one : ...;
    (* 加法可換群公理 4 + 乗法モノイド公理 3 + 分配法則 2 = 計 9 公理 *)
    ring_add_assoc / ring_add_comm / ring_add_zero_l / ring_add_neg_l : ...;
    ring_mul_assoc / ring_mul_one_l / ring_mul_one_r : ...;
    ring_distr_l / ring_distr_r : ...
  }.
  ```
- **Proof Strategy**: Record 定義のみ。公理は使用者が提供する。
- **Key Tactics**: N/A
- **Dependencies**: なし
: 1775132645:1;rocq compile integer.v integer.vo integer.vok Integer.vos 
- **Date**: 2026-04-05

---

### `ring_add_zero_r` / `ring_add_neg_r`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma ring_add_zero_r : forall (R : Ring) (a : ring_carrier R),
    ring_add R a (ring_zero R) = a.
  Lemma ring_add_neg_r : forall (R : Ring) (a : ring_carrier R),
    ring_add R a (ring_neg R a) = ring_zero R.
  ```
- **Proof Strategy**: どちらも `ring_add_comm` + 左バリアントの公理 (`ring_add_zero_l`, `ring_add_neg_l`) から直ちに得られる。
- **Key Tactics**: `rewrite ring_add_comm`, `apply ring_add_zero_l / ring_add_neg_l`
- **Dependencies**: `ring_add_comm`, `ring_add_zero_l`, `ring_add_neg_l`
- **Notes**: なし
- **Date**: 2026-04-05

---

### `ring_mul_zero_l` / `ring_mul_zero_r`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma ring_mul_zero_l : forall (R : Ring) (a : ring_carrier R),
    ring_mul R (ring_zero R) a = ring_zero R.
  Lemma ring_mul_zero_r : forall (R : Ring) (a : ring_carrier R),
    ring_mul R a (ring_zero R) = ring_zero R.
  ```
- **Proof Strategy**: `ring_add_cancel_l` + 分配法則。`0*a + 0*a = (0+0)*a = 0*a = 0*a + 0` → キャンセル則で `0*a = 0`。
- **Key Tactics**: `apply ring_add_cancel_l`, `rewrite ring_distr_r/l`, `rewrite ring_add_zero_l/r`
- **Dependencies**: `ring_add_cancel_l`, `ring_distr_r` (zero_l の場合), `ring_distr_l` (zero_r の場合)
- **Notes**: なし
- **Date**: 2026-04-05

---

### `field_no_zero_divisors`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma field_no_zero_divisors : forall (F : Field) (a b : ring_carrier F),
    ring_mul F a b = ring_zero F ->
    a = ring_zero F \/ b = ring_zero F.
  ```
- **Proof Strategy**: `classic` で `a = 0 ∨ a ≠ 0` の場合分け。`a ≠ 0` のとき `assert (H : inv(a)*(a*b) = 0)` を作り、`ring_mul_assoc` + `field_inv_l` + `ring_mul_one_l` で `b = 0` を導く。
- **Key Tactics**: `destruct (classic ...)`, `assert`, `rewrite <- ring_mul_assoc`, `rewrite field_inv_l`, `rewrite ring_mul_one_l`
- **Dependencies**: `Classic` (from Stdlib), `field_inv_l`, `ring_mul_assoc`, `ring_mul_one_l`, `ring_mul_zero_r`
- **Notes**: `rewrite <- ring_mul_assoc in H` パターンで `H : inv(a)*(a*b)` を `(inv(a)*a)*b` に変形する。
- **Date**: 2026-04-05

---

### `field_mul_cancel_l`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma field_mul_cancel_l : forall (F : Field) (a b c : ring_carrier F),
    a <> ring_zero F -> ring_mul F a b = ring_mul F a c -> b = c.
  ```
- **Proof Strategy**: `assert (H1 : inv(a)*(a*b) = inv(a)*(a*c))` → `rewrite <- ring_mul_assoc` × 2 → `rewrite field_inv_l, ring_mul_one_l` × 2。
- **Key Tactics**: `assert`, `rewrite <- ring_mul_assoc ... in H1`, `rewrite field_inv_l, ring_mul_one_l`
- **Dependencies**: `field_inv_l`, `ring_mul_assoc`, `ring_mul_one_l`
- **Notes**: ⚠️ Dead end: `ring_add_cancel_l` + `ring_neg_mul_r` + `ring_distr_l` を使った証明は途中で `ring_add_zero_r` の引数型エラーが出る。`inv(a)` を直接掛ける方が明快。
- **Date**: 2026-04-05

---

### `znz_prime_nonzero_coprime`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma znz_prime_nonzero_coprime : forall (p : nat) (a : Z),
    prime (Z.of_nat p) ->
    a mod Z.of_nat p <> 0 ->
    Z.gcd (a mod Z.of_nat p) (Z.of_nat p) = 1.
  ```
- **Proof Strategy**: `Zis_gcd_gcd` + `Zis_gcd_sym` + `prime_rel_prime`。`prime_rel_prime (Z.of_nat p) : ¬(p | r) → rel_prime r p` を適用し、仮定 `¬(p | r)` は `r ≠ 0 ∧ 0 ≤ r < p → r = k*p → k = 0 → r = 0` という矛盾で示す。
- **Key Tactics**: `apply Zis_gcd_gcd`, `apply Zis_gcd_sym`, `apply prime_rel_prime`, `destruct Hdvd as [k Hk]`, `assert (k=0) by nia`, `lia`
- **Dependencies**: `Zis_gcd_gcd`, `Zis_gcd_sym`, `prime_rel_prime`, `Z.mod_pos_bound`
- **Notes**: ⚠️ Dead end: `Z.eq_le_incl` を使った証明は型が合わない (型は `a = b → a ≤ b`)。⚠️ Dead end: `Z.mod_nonneg` は Rocq 9.1 に存在しない → `Z.mod_pos_bound` で `0 ≤ r < p` を一度に得る。⚠️ Dead end: `lra` は Import なしでは使えない → `lia` を使う。
- **Date**: 2026-04-05

---

### `Field` Record
- **Type**: Record (定義)
- **Statement**:
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
- **Proof Strategy**: Record `field_inv` は全域関数として定義し、非零の条件は公理の仮定として与える。定義の
- **Key Tactics**: N/A
- **Dependencies**: `Ring` Record
- **Notes**: `field_inv` を sigma 型 `{x | P x}` ではなく全域 `Z → Z` にすることで、具体例の定義が柔軟になる。ただし `znz_units_inv_val` は sigma 型を期待するので、具体例 `znz_p_field` では独立した epsilon ベース逆元関数が必要。
- **Date**: 2026-04-05

---

### `znz_field_inv_val`
- **Type**: Definition
- **Statement**:
  ```coq
  Definition znz_field_inv_val (p : nat) (a : {x : Z | 0 <= x < Z.of_nat p}) : Z :=
    epsilon (inhabits 0%Z)
      (fun b => 0 <= b < Z.of_nat p /\ cong p (proj1_sig a * b) 1).
  ```
- **Proof Strategy**: `epsilon` (classical choice) を使い、`znz_coprime_bezout_inv` が保証する逆元の存在から witness を取り出echo
- **Key Tactics**: `epsilon`, `inhabits`
- **Dependencies**: `cong`, `znz_coprime_bezout_inv`
- **Notes**: sigma 型の引数 `a` から `proj1_sig a` を取り出して coprimeness 条件を使う。
- **Date**: 2026-04-05

---

### `znz_field_inv_spec`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma znz_field_inv_spec : forall (p : nat) (Hp : prime (Z.of_nat p))
      (a : {x : Z | 0 <= x < Z.of_nat p}),
    proj1_sig a <> 0 ->
    0 <= znz_field_inv_val p a < Z.of_nat p /\
    cong p (proj1_sig a * znz_field_inv_val p a) 1.
  ```
- **Proof Strategy**: 1) `Z.mod_small` で `proj1_sig a mod p = proj1_sig a` を示す。2) `znz_prime_nonzero_coprime` で `gcd(proj1_sig a, p) = 1` を得る。3) `znz_coprime_bezout_inv` で逆元の存在 `∃ b, ...` を得る。4) `epsilon_spec` で `znz_field_inv_val` が条件を満たすことを確認。
- **Key Tactics**: `apply epsilon_spec`, `apply znz_coprime_bezout_inv`, `apply znz_prime_nonzero_coprime`, `rewrite Z.mod_small`
- **Dependencies**: `znz_field_inv_val`, `znz_prime_nonzero_coprime`, `znz_coprime_bezout_inv`, `epsilon_spec`
- **Notes**: ⚠️ `⟨b, Hb_range, Hb_cong⟩` は Lean 構文。Rocq では `ex_intro _ b (conj Hb_range Hb_cong)` を使う。
- **Date**: 2026-04-05

---

### `znz_p_ring`
- **Type**: Definition (Ring instance)
- **Statement**:
  ```coq
  Definition znz_p_ring (p : nat) (Hp : prime (Z.of_nat p)) : Ring.
  ```
- **Proof Strategy**: carrier = `{x : Z | 0 <= x < Z.of_nat p}` の sigma 型。全演算は mod p で正規化。`sig_eq. simpl.` 後に `Zplus_mod_idemp_*`/`Zmult_mod_idemp_*` を使う。
- **Key Tactics**: `refine {| ... |}`, `sig_eq`, `simpl`, `Zplus_mod_idemp_l/r`, `Zmult_mod_idemp_l/r`, `Z.mod_small`
- **Dependencies**: `sig_eq`, `Z.mod_pos_bound`, `Zplus_mod_idemp_l`, `Zmult_mod_idemp_l`
- **Notes**: `ring_one := exist _ (1 mod Z.of_nat p) ...`。ネストした `refine {| field_ring := {| ... |} |}` は失敗 → `znz_p_ring` を別途 `Defined` で定義してから `znz_p_field` で参照する。
- **Date**: 2026-04-05

---

### `znz_p_field`
- **Type**: Definition (Field instance)
- **Statement**:
  ```coq
  Definition znz_p_field (p : nat) (Hp : prime (Z.of_nat p)) : Field.
  ```
- **Proof Strategy**: `field_ring := znz_p_ring p Hp`。`field_inv` は inline `match Z.eq_dec (proj1_sig a) 0 with | left _ => 0-elem | right Ha => znz_field_inv_val p a-elem end`。各公理: (1) field_mul_comm: `rewrite Z.mul_comm; reflexivity`。(2) field_inv_l: `cbn [proj1_sig]` + `znz_field_inv_spec` + `Z.mod_add` + `reflexivity`。(3) field_one_ne_zero: `assert H := proj1_sig eq`、`rewrite H`、`simpl`、`Z.mod_small`、`lia`。
- **Key Tactics**: `refine {| ... |}`, `cbn [proj1_sig]`, `rewrite Z.mul_comm`, `apply znz_field_inv_spec`, `rewrite Z.mod_add`, `assert (H : proj1_sig ... = proj1_sig ...)`
- **Dependencies**: `znz_p_ring`, `znz_field_inv_val`, `znz_field_inv_spec`, `sig_eq`
: 1775132645:1;rocq compile integer.: `simpl` だけでは `proj1_sig (exist _ val ...)` が `val` に簡約されないことがある。
- **Date**: 2026-04-05

---

### `field_linear_eq_solution`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma field_linear_eq_solution : forall (F : Field) (a b : ring_carrier F),
    a <> ring_zero F ->
    ring_add F (ring_mul F a (ring_neg F (ring_mul F (field_inv F a) b))) b = ring_zero F.
  ```
- **Proof Strategy**: `ring_neg_mul_r` で右辺の neg を外に出し、`← ring_mul_assoc` で `(a * inv(a)) * b` に変形、`field_inv_r` で 1*b に、`ring_mul_one_l` で b に、`ring_add_neg_l` で 0 に。
- **Key Tactics**: `rewrite ring_neg_mul_r`, `rewrite <- ring_mul_assoc`, `rewrite field_inv_r by exact Ha`, `rewrite ring_mul_one_l`, `apply ring_add_neg_l`
- **Dependencies**: `ring_neg_mul_r`, `ring_mul_assoc`, `field_inv_r`, `ring_mul_one_l`, `ring_add_neg_l`
- **Notes**: ⚠️ Dead end: `rewrite <- ring_neg_mul_l` を途中に入れると `field_inv_r` のパターンが見つからなくなる。neg の移動は `ring_neg_mul_r` だけで十分。
- **Date**: 2026-04-05

---

### `field_linear_eq_unique`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma field_linear_eq_unique : forall (F : Field) (a b x y : ring_carrier F),
    a <> ring_zero F ->
    ring_add F (ring_mul F a x) b = ring_zero F ->
    ring_add F (ring_mul F a y) b = ring_zero F ->
    x = y.
  ```
- **Proof Strategy**: `field_mul_cancel_l` で a を消去する。そのために `ring_add_cancel_l` で b を消去して `a*x = a*y` を導く--- `b + (a*x)` の形にしてから `Hx`, `Hy` で書き換える。
- **Key Tactics**: `apply field_mul_cancel_l`, `apply ring_add_cancel_l`, `rewrite (ring_add_comm F b)`, `rewrite Hx, Hy`
- **Dependencies**: `field_mul_cancel_l`, `ring_add_cancel_l`, `ring_add_comm`
- **Notes**: `ring_add_cancel_l` の引数は消去したい項 (b) を最初に渡す。両辺を `b + ...` の形に揃えるため `ring_add_comm` を2回使う。
- **Date**: 2026-04-05

---

### `field_linear_eq_unique_solution`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem field_linear_eq_unique_solution : forall (F : Field) (a b : ring_carrier F),
    a <> ring_zero F ->
    exists! x : ring_carrier F,
      ring_add F (ring_mul F a x) b = ring_zero F.
  ```
- **Proof Strategy**: witness = `ring_neg F (ring_mul F (field_inv F a) b)`. `split` して存在は `field_linear_eq_solution`、一意性は `field_linear_eq_unique`。
- **Key Tactics**: `exists (ring_neg F ...)`, `split`, `apply field_linear_eq_solution`, `apply field_linear_eq_unique`
- **Dependencies**: `field_linear_eq_solution`, `field_linear_eq_unique`
- **Notes**: `exists!` は `unique` の略記。`split` で `P x₀` と `∀ y, P y → y = x₀` に分解される。
- **Date**: 2026-04-05

---

### `fp_linear_eq_unique_solution`
- **Type**: Corollary
- **Statement**:
  ```coq
  Corollary fp_linear_eq_unique_solution :
    forall (p : nat) (Hp : prime (Z.of_nat p))
           (a b : ring_carrier (znz_p_field p Hp)),
    a <> ring_zero (znz_p_field p Hp) ->
    exists! x : ring_carrier (znz_p_field p Hp),
      ring_add (znz_p_field p Hp) (ring_mul (znz_p_field p Hp) a x) b =
      ring_zero (znz_p_field p Hp).
  ```
- **Proof Strategy**: `field_linear_eq_unique_solution` を `znz_p_field p Hp` に直接適用するだけ。
- **Key Tactics**: `apply field_linear_eq_unique_solution`
- **Dependencies**: `field_linear_eq_unique_solution`, `znz_p_field`
- **Date**: 2026-04-05

---

### `poly_eval` / `poly_synthetic_div`
- **Type**: Definition (Fixpoint)
- **Statement**:
  ```coq
  Fixpoint poly_eval (F : Field) (f : list (ring_carrier F)) (x : ring_carrier F)
    : ring_carrier F :=
    match f with
    | [] => ring_zero F
    | c :: cs => ring_add F c (ring_mul F x (poly_eval F cs x))
    end.

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
- **Proof Strategy**: ホーナー法 (Horner) による評価と合成除算 (synthetic division)。`Field` を引数にとるため乗法可換律 `field_mul_comm` が定理で使える。
- **Key Tactics**: 定義のみ（証明なし）
- **Notes**: `Field :> Ring` コアーションにより Ring の補題も直接適用可能。`simpl poly_eval at 1` 後に `destruct` すると、Rocq が `poly_eval F [] x` を iota-reduction で自動的に `ring_zero F` に簡約してしまい、後続の `rewrite poly_eval_nil` が失敗することがある。回避策: `cbn [poly_eval poly_synthetic_div]` を使う。
- **Date**: 2026-04-05

---

### `poly_remainder_alg_A`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma poly_remainder_alg_A : forall (F : Field) (a x e : ring_carrier F),
    ring_add F (ring_mul F (ring_add F x (ring_neg F a)) e) (ring_mul F a e)
    = ring_mul F x e.
  ```
- **Proof Strategy**: `ring_distr_r` → `ring_neg_mul_l` → `ring_add_assoc` (forward) → `ring_add_neg_l` → `ring_add_zero_r`.
- **Key Tactics**: `ring_distr_r`, `ring_neg_mul_l`, `ring_add_assoc`, `ring_add_neg_l`, `ring_add_zero_r`
- **Dependencies**: `ring_distr_r`, `ring_neg_mul_l`, `ring_add_assoc`, `ring_add_neg_l`, `ring_add_zero_r`
- **Notes**: ⚠️ `ring_add_assoc` は FORWARD 方向 (`(a+b)+c → a+(b+c)`) を使う。Backward (`<-`) は失敗する。
- **Date**: 2026-04-05

---

### `poly_remainder_alg_B`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma poly_remainder_alg_B : forall (F : Field) (a x q : ring_carrier F),
    ring_mul F x (ring_mul F (ring_add F x (ring_neg F a)) q)
    = ring_mul F (ring_add F x (ring_neg F a)) (ring_mul F x q).
  ```
- **Proof Strategy**: `← ring_mul_assoc` → `field_mul_comm x (x-a)` → `ring_mul_assoc`.
- **Key Tactics**: `ring_mul_assoc`, `field_mul_comm`
- **Dependencies**: `ring_mul_assoc`, `field_mul_comm`
- **Date**: 2026-04-05

---

### `poly_remainder_core`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma poly_remainder_core : forall (F : Field) (a x e q : ring_carrier F),
    ring_add F
      (ring_mul F (ring_add F x (ring_neg F a)) (ring_add F e (ring_mul F x q)))
      (ring_mul F a e)
    = ring_mul F x (ring_add F e (ring_mul F (ring_add F x (ring_neg F a)) q)).
  ```
- **Proof Strategy**: `transitivity (x*e + xa*(x*q))`. 前半は `ring_distr_l` + `ring_add_assoc` + `ring_add_comm` + `poly_remainder_alg_A`. 後半は `symmetry` + `ring_distr_l` + `f_equal` + `poly_remainder_alg_B`。
- **Key Tactics**: `transitivity`, `ring_distr_l`, `ring_add_assoc`, `ring_add_comm`, `poly_remainder_alg_A`, `poly_remainder_alg_B`, `symmetry`, `f_equal`
- **Notes**: ⚠️ 後半 (RHS から canonical form) では `symmetry` を先に適用してから `ring_distr_l` + `f_equal` + `apply poly_remainder_alg_B` の順にすること。`apply poly_remainder_alg_B` の前に `symmetry` を忘れると unification error が出る。
- **Date**: 2026-04-05

---

### `poly_remainder_theorem`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem poly_remainder_theorem :
    forall (F : Field) (f : list (ring_carrier F)) (a x : ring_carrier F),
      poly_eval F f x =
      ring_add F
        (ring_mul F (ring_add F x (ring_neg F a))
                    (poly_eval F (poly_synthetic_div F f a) x))
        (poly_eval F f a).
  ```
- **Proof Strategy**: `f` に対するリスト帰納法（3ケース: `[]`, `[c]`, `c :: c' :: cs'`）。
  - `[]`: `ring_mul_zero_r` + `ring_add_zero_l` + `reflexivity`。
  - `[c]`: `cbn [poly_eval poly_synthetic_div]` + `repeat ring_mul_zero_r` + `ring_add_zero_l` + `reflexivity`。
  - `c :: c' :: cs'`: `rewrite poly_eval_cons` + `poly_synthetic_div_cons` + 明示的 `poly_eval_cons` × 2 + `IHcs` + `set` + `ring_add_comm` + `transitivity` + `poly_remainder_core` + `ring_add_assoc` × 2 + `ring_add_comm`。
- **Key Tactics**: `induction`, `destruct`, `cbn`, `rewrite poly_eval_cons/poly_synthetic_div_cons`, `set`, `transitivity`, `poly_remainder_core`, `ring_add_assoc`, `ring_add_comm`
- **Dependencies**: `poly_eval_cons`, `poly_synthetic_div_cons`, `poly_remainder_core`, `ring_mul_zero_r`, `ring_add_zero_l`, `ring_add_assoc`, `ring_add_comm`
- **Notes**: ⚠️ `simpl poly_eval at 1` + `destruct` `destruct` 時の iota-reduction で `poly_eval F [] x` が `ring_zero F` に自動簡約され、後続の `rewrite poly_eval_nil` や `rewrite ring_add_zero_r` が失敗する。`cbn [poly_eval poly_synthetic_div]` が安全。⚠️ singleton ケースは `cbn` + `ring_add_zero_l` + `reflexivity` のみで閉じる（`ring_add_zero_r` 2回は不要）。⚠️ `poly_eval_cons` で展開する際は、誤った occurrence を書き換えないよう引数を明示すること（例: `rewrite (poly_eval_cons F (poly_eval F (c'::cs') a) (poly_synthetic_div F (c'::cs') a) x)`）。⚠️ `set` で定義した変数（`xa` など）は `rewrite` のパターンマッチで opaque になるため、`xa` を `set` するとその後の `rewrite poly_remainder_core` が失敗する。`xa` は `set` せず `ring_add F x (ring_neg F a)` のまま使う。の組み合わせは
- **Date**: 2026-04-05

---

### `fp_remainder_theorem`
- **Type**: Corollary
- **Statement**:
  ```coq
  Corollary fp_remainder_theorem :
    forall (p : nat) (Hp : prime (Z.of_nat p))
           (f : list (ring_carrier (znz_p_field p Hp)))
           (a x : ring_carrier (znz_p_field p Hp)),
      poly_eval (znz_p_field p Hp) f x =
      ring_add (znz_p_field p Hp)
        (ring_mul (znz_p_field p Hp)
          (ring_add (znz_p_field p Hp) x (ring_neg (znz_p_field p Hp) a))
          (poly_eval (znz_p_field p Hp) (poly_synthetic_div (znz_p_field p Hp) f a) x))
        (poly_eval (znz_p_field p Hp) f a).
  ```
- **Proof Strategy**: `poly_remainder_theorem` を `znz_p_field p Hp` に適用するだけ。
- **Key Tactics**: `apply poly_remainder_theorem`
- **Dependencies**: `poly_remainder_theorem`, `znz_p_field`
- **Date**: 2026-04-05

---

### `poly_divides_linear`
- **Type**: Definition
- **Statement**:
  ```coq
  Definition poly_divides_linear (F : Field)
      (f : list (ring_carrier F)) (a : ring_carrier F) : Prop :=
    exists q : list (ring_carrier F),
      forall x : ring_carrier F,
        poly_eval F f x =
        ring_mul F (ring_add F x (ring_neg F a)) (poly_eval F q x).
  ```
- **Proof Strategy**: 命題の定義。∃ q による可除性の定式化。
- **Key Tactics**: N/A (定義)
- **Dependencies**: `poly_eval`, `ring_mul`, `ring_add`, `ring_neg`
- **Notes**: 商多項式の存在を命題として持つ。証人として `poly_synthetic_div` を使うことが多い。
- **Date**: 2026-04-05

---

### `poly_factor_of_root`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma poly_factor_of_root :
    forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
      poly_eval F f a = ring_zero F ->
      poly_divides_linear F f a.
  ```
- **Proof Strategy**: 商の証人は `poly_synthetic_div F f a`。`poly_remainder_theorem` を `rewrite` し `Hroot` で代入、`ring_add_zero_r` で末尾 0 を消去。
- **Key Tactics**: `exists`, `rewrite poly_remainder_theorem`, `rewrite Hroot`, `apply ring_add_zero_r`
- **Dependencies**: `poly_remainder_theorem`, `ring_add_zero_r`, `poly_synthetic_div`
- **Notes**: 証人を明示的に与えるので `unfold poly_divides_linear` + `exists` が必要。
- **Date**: 2026-04-05

---

### `poly_root_of_factor`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma poly_root_of_factor :
    forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
      poly_divides_linear F f a ->
      poly_eval F f a = ring_zero F.
  ```
- **Proof Strategy**: `[q Hq]` でパターンマッチ、`Hq a` で x=a を代入、`ring_add_neg_r` と `ring_mul_zero_l` を適用。
- **Key Tactics**: `intros F f a [q Hq]`, `rewrite (Hq a)`, `rewrite ring_add_neg_r`, `apply ring_mul_zero_l`
- **Dependencies**: `ring_add_neg_r`, `ring_mul_zero_l`
- **Notes**: `a - a = 0` には `ring_add_neg_r` を使う（`ring_add_neg_l` は逆順なので注意）。
- **Date**: 2026-04-05

---

### `factor_theorem`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem factor_theorem :
    forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
      poly_divides_linear F f a <-> poly_eval F f a = ring_zero F.
  ```
- **Proof Strategy**: `split` して各方向に `poly_root_of_factor` / `poly_factor_of_root` を適用するだけ。
- **Key Tactics**: `split`, `apply poly_root_of_factor`, `apply poly_factor_of_root`
- **Dependencies**: `poly_factor_of_root`, `poly_root_of_factor`
- **Notes**: 証明自体は非常に短い。基盤となる補題を正しく証明するこ
- **Date**: 2026-04-05

---

### `fp_factor_theorem`
- **Type**: Corollary
- **Statement**:
  ```coq
  Corollary fp_factor_theorem :
    forall (p : nat) (Hp : prime (Z.of_nat p))
           (f : list (ring_carrier (znz_p_field p Hp)))
           (a : ring_carrier (znz_p_field p Hp)),
      poly_divides_linear (znz_p_field p Hp) f a <->
      poly_eval (znz_p_field p Hp) f a = ring_zero (znz_p_field p Hp).
  ```
- **Proof Strategy**: `factor_theorem` を `znz_p_field p Hp` に適用するだけ。
- **Key Tactics**: `apply factor_theorem`
- **Dependencies**: `factor_theorem`, `znz_p_field`
- **Notes**: Fp への特殊化。`factor_theorem` の一行適用で終わる。
- **Date**: 2026-04-05
