# Proof Plan: euler_phi (オイラー関数)

## Goal

オイラー関数 `euler_phi` を `integer.v` に追加し、
n = p^e * q^f * r^g (p, q, r: 互いに異なる素数、e,f,g ≥ 1) のとき

  φ(n) = p^(e-1)(p-1) · q^(f-1)(q-1) · r^(g-1)(r-1)

が成立することを形式化する。

---

## 定義

```coq
(* オイラー関数: {0,...,n-1} 中で n と互素な元の個数 *)
Definition euler_phi (n : nat) : nat :=
  List.length (List.filter
    (fun k => Z.eqb (Z.gcd (Z.of_nat k) (Z.of_nat n)) 1)
    (List.seq 0 n)).
```

---

## Proof Strategy

### フェーズ 0: GroupOrder の代数的性質
GroupOrder（群の位数）の基本性質を整備する。

### フェーズ 1: euler_phi 定義 + 群位数との接続
euler_phi を定義し、znz_units_group との関係を証明する。

### フェーズ 2: 2変数単位群分解
既存 znz_units_decomp の 2 変数版を証明する。

### フェーズ 3: euler_phi の乗法性
gcd(p,q)=1 → φ(pq) = φ(p)φ(q) を証明する。

### フェーズ 4: 素数冪公式
φ(p^e) = p^(e-1)(p-1) を証明する。

### フェーズ 5: 主定理
3素数冪の公式を組み合わせて主定理を証明する。

---

## Proposed Lemmas

### フェーズ 0
- [ ] `group_order_unique`: GroupOrder G m → GroupOrder G n → m = n
- [ ] `group_order_iso`: G ≅ H → GroupOrder G m → GroupOrder H m
- [ ] `group_order_product`: GroupOrder G m → GroupOrder H n → GroupOrder (G ×ₒ H) (m*n)

### フェーズ 1
- [ ] `euler_phi` (Definition)
- [ ] `euler_phi_group_order`: GroupOrder (znz_units_group n Hn) (euler_phi n)

### フェーズ 2
- [ ] `znz_units_decomp2`: Nat.gcd p q = 1 → (Z/pqZ)* ≅ (Z/pZ)* ×ₒ (Z/qZ)*

### フェーズ 3
- [ ] `euler_phi_mul`: Nat.gcd p q = 1 → euler_phi (p*q) = euler_phi p * euler_phi q

### フェーズ 4
- [ ] `prime_pow_coprime_iff`: Nat.Prime p → (Z.gcd k (p^e) = 1 ↔ ¬ p | k)
- [ ] `count_not_divisible`: {0,...,n-1} 中の p の倍数でない元の個数 = n - n/p (p | n のとき)
- [ ] `euler_phi_prime_pow`: Nat.Prime p → 1 ≤ e → euler_phi (p^e) = p^(e-1) * (p-1)

### フェーズ 5
- [ ] `prime_pow_coprime_distinct`: Nat.Prime p → Nat.Prime q → p ≠ q → Nat.gcd (p^e) (q^f) = 1
- [ ] `euler_phi_three_prime_powers` (Main Theorem)

---

## Proof Order

1. `euler_phi` (Definition)
2. `group_order_unique`
3. `group_order_iso`
4. `group_order_product`
5. `euler_phi_group_order`
6. `znz_units_decomp2`
7. `euler_phi_mul`
8. `prime_pow_coprime_iff`
9. `count_not_divisible`
10. `euler_phi_prime_pow`
11. `prime_pow_coprime_distinct`
12. `euler_phi_three_prime_powers` (main goal)

---

## 依存関係グラフ

```
euler_phi (def)
  ↓
euler_phi_group_order   group_order_unique   group_order_iso   group_order_product
  ↓                         ↓                    ↓                  ↓
  └─────────────────── euler_phi_mul ← znz_units_decomp2
                           ↓
               prime_pow_coprime_iff
               count_not_divisible
                           ↓
               euler_phi_prime_pow ← prime_pow_coprime_distinct
                           ↓
               euler_phi_three_prime_powers
```

---

## Stdlib 使用予定

- `Nat.Prime`, `Nat.prime_def_lt_prime`, `Nat.Prime_alt`
- `List.filter`, `List.length`, `List.seq`
- `Z.gcd`, `Z.eqb`
- `Nat.pow`, `Nat.div`, `Nat.gcd`
- `Nat2Z.inj_pow`, `Nat2Z.inj_mul`
