# Proof Plan: subgroup_of_cyclic

## Goal

```coq
Theorem subgroup_of_cyclic :
  forall (C : CyclicGroup) (m : nat) (H : Subgroup C),
  GroupOrder C m ->
  (* (1) H は巡回群 *)
  (exists gen : carrier C,
     subgroup_pred C H gen /\
     forall x : carrier C,
       subgroup_pred C H x ->
       exists n : Z, gpow C gen n = x) /\
  (* (2) H の位数は m の約数 *)
  (exists k : nat,
     (0 < k)%nat /\
     Nat.divide k m /\
     GroupOrder (subgroup_group C H) k).
```

## 数学的な証明方針

`g = generator C` とおく。

### Part 1: H は巡回群

1. `generator_order` より `g^m = e`。`contains_e` より `e ∈ H` なので `g^m ∈ H`。
2. `S := { n ∈ ℕ | n > 0 ∧ g^n ∈ H }` とおく。S は非空（m ∈ S）。
3. 整列原理 (well-ordering) により S の最小元 d が存在する。`0 < d`、`g^d ∈ H`、かつ `∀ k, 0 < k → g^k ∈ H → d ≤ k`。
4. `gen := g^d` が H を生成することを示す:
   - `gen ∈ H`: d の定義より。
   - `∀ x ∈ H, ∃ q : ℤ, (g^d)^q = x`:
     - `cyclic_property` より `x = g^z` なる `z : ℤ` が存在する。
     - Euclidean 除算: `z = q * d + r`、`0 ≤ r < d`（`Z.div_mod` 使用）。
     - `g^r = g^z * (g^d)^(-q) ∈ H`（`gpow_in_subgroup` による H の閉性）。
     - `r > 0` なら `r ∈ S` かつ `r < d`、d の最小性に矛盾。よって `r = 0`。
     - `x = g^(qd) = (g^d)^q`。

### Part 2: |H| は m の約数

1. **d | m の証明**: 同様の Euclidean 除算を m に適用。`g^m = e ∈ H` より `m ∈ S`。`m = q*d + r` のとき `g^r ∈ H` かつ `r < d`、最小性より `r = 0`、よって `d | m`。
2. **|H| = m/d の証明**: 写像 `i ↦ g^(d*i)` が `Fin.t (m/d) → H` の全単射であることを示す。
   - H の各元は Part 1 より `g^(nd)` の形。n を `m/d` で割ると余り `r < m/d` が得られ、`x = g^(dr)`。
   - `g^(di) = g^(dj)` ならば `g^(d*(j-i)) = e` であり、`0 < d*(j-i) < m` ならば `cyclic_group_order_le_period` に矛盾。よって `i = j`（単射性）。

## 補助定理一覧（証明順序）

### 補題 1: `gpow_in_subgroup`
```coq
Lemma gpow_in_subgroup :
  forall (G : Group) (H : Subgroup G) (x : carrier G),
    subgroup_pred G H x ->
    forall n : Z, subgroup_pred G H (gpow G x n).
```
証明: `n` の符号で場合分け。正の場合は `closed_op`、負の場合は `closed_inv` を使う帰納法。

---

### 補題 2: `group_order_pos`
```coq
Lemma group_order_pos :
  forall (G : Group) (m : nat),
    GroupOrder G m -> (0 < m)%nat.
```
証明: `e` を `f` で写すと `f e : Fin.t m` が存在する。`Fin.t m` が非空なので `m > 0`。

---

### 補題 3: `well_ordering_nat`
```coq
Lemma well_ordering_nat :
  forall (P : nat -> Prop),
    (exists n, P n) ->
    exists d, P d /\ forall k, (k < d)%nat -> ~ P k.
```
証明: 強帰納法。`n` を P の証人として、0 から n まで P を満たす最小の自然数を選ぶ。`classic` を用いて「P k が成り立つ最小の k」を得る。

---

### 補題 4: `generator_period_divides_nat`
```coq
Lemma generator_period_divides_nat :
  forall (C : CyclicGroup) (m k : nat),
    GroupOrder C m ->
    gpow C (generator C) (Z.of_nat k) = e C ->
    Nat.divide m k.
```
証明: `k = q * m + r`（`0 ≤ r < m`）と Euclidean 除算。`g^k = e` より `g^r = e`。`r > 0` なら `cyclic_group_order_le_period` により `m ≤ r < m` で矛盾。よって `r = 0`、`m | k`。

---

### 補題 5: `min_period_in_subgroup`
```coq
Lemma min_period_in_subgroup :
  forall (C : CyclicGroup) (m : nat) (H : Subgroup C),
    GroupOrder C m ->
    exists d : nat,
      (0 < d)%nat /\
      subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) /\
      forall k : nat,
        (0 < k)%nat ->
        subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
        (d <= k)%nat.
```
証明: `P n := (0 < n ∧ g^n ∈ H)` に `well_ordering_nat` を適用。`generator_order` + `contains_e` より `P m` が成立し、P の証人 m が存在する。

---

### 補題 6: `subgroup_element_is_power_of_d`
```coq
Lemma subgroup_element_is_power_of_d :
  forall (C : CyclicGroup) (m : nat) (H : Subgroup C) (d : nat),
    GroupOrder C m ->
    (0 < d)%nat ->
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    (forall k : nat, (0 < k)%nat ->
      subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
      (d <= k)%nat) ->
    forall x : carrier C,
      subgroup_pred C H x ->
      exists n : Z, gpow C (gpow C (generator C) (Z.of_nat d)) n = x.
```
証明: `cyclic_property` + Euclidean 除算 + `gpow_in_subgroup` + d の最小性。

---

### 補題 7: `min_period_divides_group_order`
```coq
Lemma min_period_divides_group_order :
  forall (C : CyclicGroup) (m : nat) (H : Subgroup C) (d : nat),
    GroupOrder C m ->
    (0 < d)%nat ->
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    (forall k : nat, (0 < k)%nat ->
      subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
      (d <= k)%nat) ->
    Nat.divide d m.
```
証明: `generator_order` により `g^m = e ∈ H`。同様の Euclidean 除算で `d | m`。

---

### 補題 8: `m_div_d_pos`
```coq
Lemma m_div_d_pos :
  forall (m d : nat),
    (0 < m)%nat ->
    (0 < d)%nat ->
    Nat.divide d m ->
    (0 < m / d)%nat.
```
証明: `Nat.divide` の定義と `Nat.div_pos`（または `lia`）。

---

### 補題 9: `powers_of_gd_in_subgroup`
```coq
Lemma powers_of_gd_in_subgroup :
  forall (C : CyclicGroup) (H : Subgroup C) (d : nat) (i : Z),
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    subgroup_pred C H (gpow C (generator C) (i * Z.of_nat d)).
```
証明: `gpow_mul` で `(g^d)^i` に変形し、`gpow_in_subgroup` を適用。

---

### 補題 10: `powers_of_gd_distinct`
```coq
Lemma powers_of_gd_distinct :
  forall (C : CyclicGroup) (m d i j : nat),
    GroupOrder C m ->
    (0 < d)%nat ->
    Nat.divide d m ->
    (i < j)%nat ->
    (j < m / d)%nat ->
    gpow C (generator C) (Z.of_nat (d * i)) <>
    gpow C (generator C) (Z.of_nat (d * j)).
```
証明: 等しいと仮定すると `equal_powers_imply_period` より `g^(d*(j-i)) = e`。`0 < d*(j-i) < m` なので `cyclic_group_order_le_period` により `m ≤ d*(j-i) < m`、矛盾。

---

### 補題 11: `every_subgroup_element_is_small_power`
```coq
Lemma every_subgroup_element_is_small_power :
  forall (C : CyclicGroup) (m d : nat) (H : Subgroup C),
    GroupOrder C m ->
    (0 < d)%nat ->
    Nat.divide d m ->
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    (forall k : nat, (0 < k)%nat ->
      subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
      (d <= k)%nat) ->
    forall x : carrier C,
      subgroup_pred C H x ->
      exists r : nat,
        (r < m / d)%nat /\
        x = gpow C (generator C) (Z.of_nat (d * r)).
```
証明: `subgroup_element_is_power_of_d` で `x = (g^d)^n` を得る。`gpow_mul` で `x = g^(nd)` に変形。Z の Euclidean 除算で `n = q * (m/d) + r`（0 ≤ r < m/d）。`x = g^(nd) = g^(q*m + rd) = g^(rd)` を `gpow_add`, `gpow_mul`, `generator_order`, `gpow_e` を用いて示す。

---

### 補題 12: `subgroup_group_order`
```coq
Lemma subgroup_group_order :
  forall (C : CyclicGroup) (m d : nat) (H : Subgroup C),
    GroupOrder C m ->
    (0 < d)%nat ->
    Nat.divide d m ->
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    (forall k : nat, (0 < k)%nat ->
      subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
      (d <= k)%nat) ->
    GroupOrder (subgroup_group C H) (m / d).
```
証明方針: 全単射 `f : {x | x ∈ H} → Fin.t (m/d)` を構成する。

`every_subgroup_element_is_small_power` により各 `x ∈ H` は唯一の `r < m/d` で `x = g^(dr)` と表せる。

- **関数の構成**: `f(x, Hx)` を、`every_subgroup_element_is_small_power` から得られる余り `r` として `Fin.of_nat r (m/d-1)` と定義したいが、`r` の一意性が必要。  
  一意性は `powers_of_gd_distinct` より保証される（2つの r が等しくなければ g^(dr) ≠ g^(dr')、矛盾）。  
  古典論理を用いて `ClassicalDescription.constructive_indefinite_description` で証人を確定的に取り出す。

- **単射性**: `f(x) = f(y)` ならば同じ `r` を持つので `x = g^(dr) = y`。

- **全射性**: 任意の `i : Fin.t (m/d)` に対して `x := g^(d * Fin.to_nat i) ∈ H`（`powers_of_gd_in_subgroup`）であり `f(x) = i`。

**注意**: `ClassicalDescription` モジュールのインポートが必要になる可能性がある。代替として、`f` の定義に `Fin_injective_le` と全射性を分けて示す方法も検討する。

---

## 証明順序

1. `gpow_in_subgroup`
2. `group_order_pos`
3. `well_ordering_nat`
4. `generator_period_divides_nat`
5. `min_period_in_subgroup`
6. `subgroup_element_is_power_of_d`
7. `min_period_divides_group_order`
8. `m_div_d_pos`
9. `powers_of_gd_in_subgroup`
10. `powers_of_gd_distinct`
11. `every_subgroup_element_is_small_power`
12. `subgroup_group_order`
13. `subgroup_of_cyclic` (主定理の組み立て)

## 技術的な注意事項

- `gpow_in_subgroup` は `gpow_mul`、`gpow_of_nat`、`gpow_neg_of_nat` を活用する。
- `well_ordering_nat` の証明には `classic` (from `Classical`) を用いた強帰納法を使う。
- `generator_period_divides_nat` は `gpow_reduce_mod` と `cyclic_group_order_le_period` の組み合わせ。
- `subgroup_group_order` の `f` の定義が最も技術的に困難な部分。`ClassicalDescription` か `IndefiniteDescription` のインポートを検討。または、`f` の全単射を間接的に（`Fin_injective_le` + 逆方向の不等式で）示す。
- `subgroup_group C H` の carrier は `{x : carrier C | subgroup_pred C H x}` (sigma type) で、`sig_eq` で等式を示す。
