## 完成 (2025年)

--------国剰余定理の証明が完成した。以下のすべての補題と定理が integer.v に証明済みで追加された。

| Lemma/Theorem | 状態 |
|---|---|
| Z_of_nat_divide_aux | ✅ 証明済 |
| nat_coprime_bezout | ✅ 証明済 |
| cong_of_mod | ✅ 証明済 |
| mod_of_cong | ✅ 証明済 |
| cong_unique_in_range | ✅ 証明済 |
| cong_trans | ✅ 証明済 |
| coprime_divide_mul | ✅ 証明済 |
| crt_mod_pq | ✅ 証明済 |
| crt_solution_cong | ✅ 証明済 |
| crt_exists | ✅ 証明済 |
| crt_unique | ✅ 証明済 |
| chinese_remainder | ✅ 証明済 |

---

# Proof Plan: chinese_remainder

## Goal

```coq
Theorem chinese_remainder :
  forall (p q : nat) (a b : Z),
    (0 < p)%nat ->
    (0 < q)%nat ->
    Nat.gcd p q = 1 ->
    0 <= a < Z.of_nat p ->
    0 <= b < Z.of_nat q ->
    exists! n : Z,
      0 <= n < Z.of_nat (p * q) /\
      n mod Z.of_nat p = a /\
      n mod Z.of_nat q = b.
```

## 数学的な証明方針

### 存在性

Bézout の定理より `gcd(p, q) = 1` から `p*x + q*y = 1` を満たす整数 `x, y` が存在する。

候補解: `n₀ := a * q * y + b * p * x`

- `n₀ mod p = a`：`q*y ≡ 1 (mod p)`（∵ `p*x + q*y = 1` より）、`b*p*x ≡ 0 (mod p)` なので `n₀ ≡ a (mod p)`
- `n₀ mod q = b`：`p*x ≡ 1 (mod q)` より同様

`n := n₀ mod (p*q)` と定義すると `0 ≤ n < p*q` が成り立ち、かつ `n ≡ n₀ (mod p)` および `n ≡ n₀ (mod q)` なので元の合同式を保つ。

### 一意性

`n₁, n₂` がともに条件を満たすとすると:
- `n₁ ≡ n₂ (mod p)` かつ `n₁ ≡ n₂ (mod q)`
- `gcd(p, q) = 1` より `p*q | (n₁ - n₂)`
- `0 ≤ n₁, n₂ < p*q` なので `|n₁ - n₂| < p*q`
- よって `n₁ - n₂ = 0`、すなわち `n₁ = n₂`

## 補助定理一覧（証明順序）

### 補題 1: `nat_coprime_bezout`

```coq
Lemma nat_coprime_bezout : forall (p q : nat),
  Nat.gcd p q = 1 ->
  exists x y : Z, Z.of_nat p * x + Z.of_nat q * y = 1.
```

証明:
1. `Nat2Z.inj_gcd` (stdlib) により `Z.of_nat (Nat.gcd p q) = Z.gcd (Z.of_nat p) (Z.of_nat q)`
2. `Nat.gcd p q = 1` を代入して `Z.gcd (Z.of_nat p) (Z.of_nat q) = 1`
3. `linear_diophantine` に `d = 1` を適用（`1 | 1` は自明）

---

### 補題 2: `cong_of_mod`

```coq
Lemma cong_of_mod : forall (m : nat) (n a : Z),
  (0 < m)%nat ->
  n mod Z.of_nat m = a ->
  n ≡ a [mod m].
```

証明:
- `n = Z.of_nat m * (n / Z.of_nat m) + a` より `n - a = Z.of_nat m * (n / Z.of_nat m)`
- よって `Z.of_nat m | (n - a)`、つまり `n ≡ a [mod m]`
- 使用: `Z.div_mod`

---

### 補題 3: `mod_of_cong`

```coq
Lemma mod_of_cong : forall (m : nat) (n a : Z),
  (0 < m)%nat ->
  0 <= a < Z.of_nat m ->
  n ≡ a [mod m] ->
  n mod Z.of_nat m = a.
```

証明:
- `n ≡ a [mod m]` から `m | (n - a)`
- `n mod m = (n - a + a) mod m = a mod m = a`（`0 ≤ a < m` より `Z.mod_small`）
- 使用: `Z.mod_eq`, `Z.mod_small`, `Z.divide` の定義展開

---

### 補題 4: `cong_unique_in_range`

```coq
Lemma cong_unique_in_range : forall (m : nat) (a b : Z),
  (0 < m)%nat ->
  0 <= a < Z.of_nat m ->
  0 <= b < Z.of_nat m ->
  a ≡ b [mod m] ->
  a = b.
```

証明:
- `m | (a - b)` かつ `-(m-1) ≤ a - b ≤ m-1`
- `Z.divide` の定義より `a - b = m * k` かつ `|m*k| < m` → `k = 0`
- 使用: `Z.divide` 展開, `lia`

---

### 補題 5: `coprime_divide_mul`

```coq
Lemma coprime_divide_mul : forall (p q : nat) (a : Z),
  Nat.gcd p q = 1 ->
  (Z.of_nat p | a) ->
  (Z.of_nat q | a) ->
  (Z.of_nat p * Z.of_nat q | a).
```

証明:
- `nat_coprime_bezout` より `∃ x y, p*x + q*y = 1`
- `a = a * 1 = a*(p*x + q*y) = a*p*x + a*q*y`
- `q | a` より `a = q*k`、よって `a*p*x = q*k*p*x`、`p*q | a*p*x`
- `p | a` より `a = p*j`、よって `a*q*y = p*j*q*y`、`p*q | a*q*y`
- `p*q | a`
- 使用: `Z.divide_add_r`, `Z.divide_mul_l`

---

### 補題 6: `crt_mod_pq`

```coq
Lemma crt_mod_pq : forall (p q : nat) (n : Z),
  (0 < p)%nat ->
  (0 < q)%nat ->
  n mod (Z.of_nat p * Z.of_nat q) ≡ n [mod p] /\
  n mod (Z.of_nat p * Z.of_nat q) ≡ n [mod q].
```

証明:
- `n = (p*q) * k + r`（r = n mod (p*q)）より `n - r = (p*q) * k`
- `p | (p*q)` かつ `q | (p*q)` より `p | (n - r)` かつ `q | (n - r)`
- 使用: `Z.divide_mul_l`, `Z.div_mod`

---

### 補題 7: `crt_solution_cong`

```coq
Lemma crt_solution_cong : forall (p q : nat) (a b x y : Z),
  (0 < p)%nat ->
  (0 < q)%nat ->
  Z.of_nat p * x + Z.of_nat q * y = 1 ->
  let n0 := a * Z.of_nat q * y + b * Z.of_nat p * x in
  n0 ≡ a [mod p] /\ n0 ≡ b [mod q].
```

証明:
- `n0 mod p`：`b * p * x ≡ 0 (mod p)`（`p | p*x`）、`a * q * y ≡ a * 1 = a (mod p)`（∵ `q*y = 1 - p*x ≡ 1 (mod p)`）
- `n0 mod q`：対称的に `a * q * y ≡ 0 (mod q)`, `b * p * x ≡ b (mod q)`
- 使用: `cong_mul`, `cong_add`, `cong_sub`, `Z.divide_mul_l`

---

### 補題 8: `crt_exists`

```coq
Lemma crt_exists : forall (p q : nat) (a b : Z),
  (0 < p)%nat ->
  (0 < q)%nat ->
  Nat.gcd p q = 1 ->
  0 <= a < Z.of_nat p ->
  0 <= b < Z.of_nat q ->
  exists n : Z,
    0 <= n < Z.of_nat (p * q) /\
    n mod Z.of_nat p = a /\
    n mod Z.of_nat q = b.
```

証明:
1. `nat_coprime_bezout` で `∃ x y, p*x + q*y = 1`
2. `n0 := a * q * y + b * p * x`; `n := n0 mod (p*q)`
3. `Z.mod_pos_bound` より `0 ≤ n < p*q`（`Nat2Z.inj_mul` で `Z.of_nat (p*q) = p*q`）
4. `crt_solution_cong` + `crt_mod_pq` より `n ≡ a (mod p)` および `n ≡ b (mod q)`
5. `mod_of_cong` で `n mod p = a` および `n mod q = b` に変換

---

### 補題 9: `crt_unique`

```coq
Lemma crt_unique : forall (p q : nat) (a b n1 n2 : Z),
  (0 < p)%nat ->
  (0 < q)%nat ->
  Nat.gcd p q = 1 ->
  0 <= n1 < Z.of_nat (p * q) ->
  0 <= n2 < Z.of_nat (p * q) ->
  n1 mod Z.of_nat p = a ->
  n1 mod Z.of_nat q = b ->
  n2 mod Z.of_nat p = a ->
  n2 mod Z.of_nat q = b ->
  n1 = n2.
```

証明:
1. `cong_of_mod` で `n1 ≡ a (mod p)`, `n2 ≡ a (mod p)` → `n1 ≡ n2 (mod p)`
2. 同様に `n1 ≡ n2 (mod q)`
3. `coprime_divide_mul` より `p*q | (n1 - n2)`
4. `0 ≤ n1, n2 < p*q` より `|n1 - n2| < p*q`
5. よって `n1 - n2 = 0`
- 使用: `cong_sub`, `coprime_divide_mul`, `Z.divide` 展開, `lia`

---

### 主定理: `chinese_remainder`

```coq
Theorem chinese_remainder :
  forall (p q : nat) (a b : Z),
    (0 < p)%nat ->
    (0 < q)%nat ->
    Nat.gcd p q = 1 ->
    0 <= a < Z.of_nat p ->
    0 <= b < Z.of_nat q ->
    exists! n : Z,
      0 <= n < Z.of_nat (p * q) /\
      n mod Z.of_nat p = a /\
      n mod Z.of_nat q = b.
```

証明:
- `crt_exists` で存在性
- `crt_unique` で一意性
- `exists!` の unfold と組み合わせ

---

## 証明順序

1. `nat_coprime_bezout`
2. `cong_of_mod`
3. `mod_of_cong`
4. `cong_unique_in_range`
5. `coprime_divide_mul`
6. `crt_mod_pq`
7. `crt_solution_cong`
8. `crt_exists`
9. `crt_unique`
10. `chinese_remainder`（主定理）

## 技術的な注意事項

- `Nat2Z.inj_gcd` が stdlib に存在するか確認する（`Require Import ZArith` に含まれる可能性あり）。存在しない場合は個別に証明が必要。
- `Z.of_nat (p * q) = Z.of_nat p * Z.of_nat q` の変換に `Nat2Z.inj_mul` を使用。
- `cong` は `(Z.of_nat m | a - b)` として定義されているため、`Z.modulo` との橋渡し補題（補題 2, 3）が必要。
- `crt_mod_pq` で `n mod (p*q) ≡ n (mod p)` を示す際、`Z.divide_mul_l` と `Z.divide_mul_r` を活用。
- `coprime_divide_mul` の証明で `Z.of_nat p * Z.of_nat q` が `integer.v` の `cong` 定義の形式と合うよう注意（`Nat2Z.inj_mul` で変換）。
- 主定理の `exists!` は `exists n, P n /\ forall m, P m -> m = n` と同値なので unfold して扱う。
