# Proof Plan: znz_units_decomp（既約剰余類群の分解定理）

## Goal

```coq
Theorem znz_units_decomp :
  forall (p q r : nat) (Hp : (1 < p)%nat) (Hq : (1 < q)%nat) (Hr : (1 < r)%nat)
    (Hpqr : (1 < p * q * r)%nat),
    pairwise_coprime3 p q r ->
    znz_units_group (p * q * r) Hpqr ≅
    znz_units_group p Hp ×ₒ znz_units_group q Hq ×ₒ znz_units_group r Hr.
```

n = p * q * r, p q r が pairwise coprime のとき、(Z/nZ)* ≅ (Z/pZ)* × (Z/qZ)* × (Z/rZ)*。
ユーザーの言う「n = p^e * q^f * r^g」の場合は p, q, r を素数ベキに置き換えた特殊ケース。

## 写像

```
φ : (Z/pqrZ)* → ((Z/pZ)* × (Z/qZ)*) × (Z/rZ)*
φ([a]) = (([a mod p], [a mod q]), [a mod r])
```

各成分 [a mod p] の carrier 条件:
- 範囲: Z.mod_pos_bound
- 互素: znz_units_gcd_dvd + znz_gcd_mod_eq (新規補題が必要)

## Proof Strategy

`IsIsomorphism` の定義に従い `exists phi` で写像を与え、
準同型性・単射性・全射性の3つを個別に証明する。

- **準同型性**: (a*b) mod pqr mod p = (a mod p * b mod p) mod p （znz_units_decomp_mul_mod）
- **単射性**: crt_unique_3（znz_decomp と同様の構造）
- **全射性**: crt_exists_3 で n を構成し、znz_units_gcd_mul3 で gcd(n, pqr) = 1 を示す

## Proposed Lemmas

- [ ] `znz_units_gcd_dvd`: gcd(a, m*n) = 1 → gcd(a, m) = 1
- [ ] `znz_units_gcd_mul`: gcd(a,m) = 1 ∧ gcd(a,n) = 1 → gcd(a,m*n) = 1 (rel_prime_mult 使用)
- [ ] `znz_units_coprime_mod_l`: gcd(a, p*q*r) = 1 → gcd(a mod p, p) = 1
- [ ] `znz_units_coprime_mod_m`: gcd(a, p*q*r) = 1 → gcd(a mod q, q) = 1
- [ ] `znz_units_coprime_mod_r`: gcd(a, p*q*r) = 1 → gcd(a mod r, r) = 1
- [ ] `znz_units_gcd_mul3`: gcd(a,p)=1 ∧ gcd(a,q)=1 ∧ gcd(a,r)=1 → gcd(a, p*q*r) = 1
- [ ] `znz_units_decomp_mul_mod`: (a*b) mod pqr mod p = (a mod p * b mod p) mod p
- [ ] `znz_units_decomp`: 主定理

## Proof Order

1. `znz_units_gcd_dvd`
2. `znz_units_gcd_mul`
3. `znz_units_coprime_mod_l`
4. `znz_units_coprime_mod_m`
5. `znz_units_coprime_mod_r`
6. `znz_units_gcd_mul3`
7. `znz_units_decomp_mul_mod`
8. `znz_units_decomp` (main goal)

## 利用する既存補題

| 補題 | 用途 |
|------|------|
| `znz_gcd_mod_eq` | gcd(a mod n, n) = gcd(a, n) |
| `znz_gcd_mul_coprime` | gcd(a*b, n) = 1 (乗算閉包) |
| `znz_mod_mod_l/m/r` | (a mod pqr) mod p = a mod p 等 |
| `pairwise_coprime3` | pairwise coprime 条件 |
| `crt_exists_3` | 全射性の逆像構成 |
| `crt_unique_3` | 単射性の一意性 |
| `sig_eq` | sigma 型の等号 |
| `Zis_gcd_gcd`, `Zgcd_is_gcd`, `Zis_gcd_sym` | gcd ↔ Zis_gcd 変換 |
| `rel_prime_mult` | rel_prime 乗算閉包 |
| `Z.divide_mul_r` | d\|m → d\|m*n |
| `Z.mul_mod` | (a*b) mod n = (a mod n * b mod n) mod n |
| `Nat2Z.inj_mul` | Z.of_nat (m*n) = Z.of_nat m * Z.of_nat n |
