# Proof Plan: znz_decomp

## Goal

```coq
Theorem znz_decomp :
  forall (p q r : nat) (Hp : (0 < p)%nat) (Hq : (0 < q)%nat) (Hr : (0 < r)%nat),
    pairwise_coprime3 p q r ->
    znz_group (p * q * r) (Nat.mul_pos (Nat.mul_pos Hp Hq) Hr) ≅
    znz_group p Hp ×ₒ znz_group q Hq ×ₒ znz_group r Hr.
```

n = p*q*r、p,q,r が pairwise coprime のとき、Z/(pqr)Z ≅ Z/pZ × Z/qZ × Z/rZ を示す。

## 写像

φ : Z/(pqr)Z → (Z/pZ × Z/qZ) × Z/rZ  
φ([a]) = (([a mod p], [a mod q]), [a mod r])

`group_product` は左結合なので型は `((znz_group p) ×ₒ (znz_group q)) ×ₒ (znz_group r)`。

## Proof Strategy

`IsIsomorphism` の定義（準同型性・単射性・全射性）を `exists φ` で与える。

- **準同型性**: `(a+b) mod n mod p = ((a mod p)+(b mod p)) mod p`  
  stdlib の `mod_mod_divide` を使う。
- **単射性**: `crt_unique_3` から `a = b`（as Z 値）を導く。
- **全射性**: `crt_exists_3` で任意の (x,y,z) の逆像を構成する。

## Proposed Lemmas

- [ ] `znz_dvd_mul3_l`: `(Z.of_nat p | Z.of_nat (p * q * r))`
- [ ] `znz_dvd_mul3_m`: `(Z.of_nat q | Z.of_nat (p * q * r))`
- [ ] `znz_dvd_mul3_r`: `(Z.of_nat r | Z.of_nat (p * q * r))`
- [ ] `znz_decomp_hom`: 準同型性
- [ ] `znz_decomp_inj`: 単射性
- [ ] `znz_decomp_surj`: 全射性
- [ ] `znz_decomp`: 主定理

## Proof Order

1. `znz_dvd_mul3_l`
2. `znz_dvd_mul3_m`
3. `znz_dvd_mul3_r`
4. `znz_decomp_hom`
5. `znz_decomp_inj`
6. `znz_decomp_surj`
7. `znz_decomp` (main goal)

## 利用する既存補題

| 補題 | 用途 |
|------|------|
| `mod_mod_divide` (stdlib Zdiv) | `(c|b) -> (a mod b) mod c = a mod c` |
| `Zplus_mod` | `(a+b) mod n = ((a mod n)+(b mod n)) mod n` |
| `crt_unique_3` | 単射性の証明 |
| `crt_exists_3` | 全射性の証明 |
| `pairwise_coprime3_*` | pairwise coprime から各 gcd 仮定を取り出す |
| `sig_eq` | sigma 型の等号 |
| `cong_of_mod`, `mod_of_cong` | mod ↔ cong 変換 |
| `cong_trans` | 合同の推移律 |
