# generator_order 証明進捗

## 目標

```coq
Lemma generator_order : forall (C : CyclicGroup) (m : nat),
  GroupOrder C m ->
  gpow C (generator C) (Z.of_nat m) = e C.
```

## 証明の全体方針 (generator_order.md より)

1. `GroupOrder C m` から全単射 `f : carrier C → Fin.t m` を取り出す
2. 鳩ノ巣原理: `g^0, g^1, ..., g^m` を `f` で写すと `Fin.t m` に `m+1` 個 → 重複あり
3. 重複から周期 `d` (0 < d ≤ m) を得: `g^d = e`
4. 巡回性より群の元はすべて `g^0, ..., g^(d-1)` で表せる → `m ≤ d`
5. `d ≤ m` かつ `m ≤ d` より `d = m` → `g^m = e`

---

## 完了した補題

### `op_cancel_l` ✅ (integer.v に追加済み)

```coq
Lemma op_cancel_l : forall (G : Group) (x y z : carrier G),
  op G x y = op G x z -> y = z.
```

左消去則。両辺に左から `inv(x)` を掛け、結合律・左逆元・左単位元を適用して証明。
`equal_powers_imply_period` の核心部分で使用する。

### `equal_powers_imply_period` ✅ (integer.v に追加済み)

```coq
Lemma equal_powers_imply_period :
  forall (G : Group) (a : carrier G) (i j : nat),
    (i < j)%nat ->
    gpow G a (Z.of_nat i) = gpow G a (Z.of_nat j) ->
    gpow G a (Z.of_nat (j - i)) = e G.
```

両辺の左から `g^i` を掛け、`gpow_add` で `g^i * g^(j-i) = g^j = g^i`、`op_cancel_l` で消去。
注: `Open Scope Z_scope` のため `i < j` は `(i < j)%nat` と明示が必要。

---

## 完了 (2026-04-03 追加分)

### `fin_all` 関連補題 ✅
- `fin_all_length`, `fin_all_complete`, `fin_all_NoDup`

### `not_NoDup_has_dup` ✅
### `Fin_injective_le` ✅
### `pigeonhole_Fin` ✅
### `pigeonhole_powers` ✅
### `gpow_reduce_mod` ✅
### `cyclic_group_order_le_period` ✅
### `group_order_bijection` ✅
### `generator_order` ✅ **証明完了**

---

## (旧) TODO (すべて完了)

```coq
Lemma pigeonhole_Fin :
  forall (m : nat) (h : nat -> Fin.t m),
    exists i j : nat,
      i < j /\ j <= m /\ h i = h j.
```

**方針:**
- `h 0, h 1, ..., h m` は `m+1` 個の値を `Fin.t m` (m 要素) に送る
- `Fin.t m` への単射は高々 m 個 → 重複必至
- Stdlib の `Fin.t` に関する決定的等号 (`Fin.eq_dec`) を使って探索

実装は Rocq でやや重い部分。最初は `Admitted` にして先へ進んでもよい。

依存: `Stdlib.Vectors.Fin`, `Fin.eq_dec`

---

### Step 3: `pigeonhole_powers` (鳩ノ巣 + 冪の組み合わせ)

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

**方針:**
- `h k := f (gpow C (generator C) (Z.of_nat k))` を定義
- `pigeonhole_Fin` で重複する `i < j ≤ m` を得る
- `f` の単射性から `g^i = g^j` を導く

依存: `pigeonhole_Fin`, `GroupOrder` の単射性

---

### Step 4: `gpow_period_multiple` (周期の倍数は単位元)

```coq
Lemma gpow_period_multiple :
  forall (G : Group) (a : carrier G) (d q : nat),
    gpow G a (Z.of_nat d) = e G ->
    gpow G a (Z.of_nat (q * d)) = e G.
```

**方針:**
- `gpow_mul` で `g^(q*d) = (g^d)^q`
- `g^d = e` を代入 → `e^q = e` (`gpow_nat_e`)

依存: `gpow_mul`, `gpow_nat_e`

---

### Step 5: `cyclic_group_order_le_period` (周期から位数の上界)

```coq
Lemma cyclic_group_order_le_period :
  forall (C : CyclicGroup) (m d : nat),
    GroupOrder C m ->
    0 < d ->
    gpow C (generator C) (Z.of_nat d) = e C ->
    m <= d.
```

**方針:**
- 任意の `x : carrier C` に対して `cyclic_property` より `x = g^z` (z : Z)
- `z` を `d` で割って `z = q*d + r` (0 ≤ r < d)
- `g^z = g^(q*d) * g^r = e * g^r = g^r` (`gpow_period_multiple`, `gpow_add`)
- よって全元が `{g^0, ..., g^(d-1)}` の中に入る → 高々 `d` 個
- `GroupOrder C m` の全単射性と合わせて `m ≤ d`

依存: `gpow_add`, `gpow_period_multiple`, `GroupOrder`

---

### Step 6: `generator_order` の組み立て (最終)

```coq
Lemma generator_order : forall (C : CyclicGroup) (m : nat),
  GroupOrder C m ->
  gpow C (generator C) (Z.of_nat m) = e C.
```

**方針:**
1. `GroupOrder C m` から単射 `f` を取り出す
2. `pigeonhole_powers` で `i < j ≤ m`, `g^i = g^j` を得る
3. `equal_powers_imply_period` で `d := j - i`, `g^d = e`, `0 < d ≤ m`
4. `cyclic_group_order_le_period` で `m ≤ d`
5. `d ≤ m` と合わせて `d = m` → `g^m = e`

---

## 難所メモ

- **`pigeonhole_Fin`**: Rocq で素朴に書くと証明が重くなりがち。`Fin.eq_dec` と帰納法の組み合わせが必要。最初は `Admitted` で後回しにするのが現実的。
- **`cyclic_group_order_le_period`**: 整数指数 `z : Z` を自然数の余り `r < d` に落とす部分で `Z.div_mod` や `gpow_add`, `gpow_mul` を複数組み合わせる必要がある。
