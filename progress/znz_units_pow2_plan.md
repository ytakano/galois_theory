# Proof Plan: znz_units_pow2_structure

## Goal

```coq
Theorem znz_units_pow2_structure :
  forall (n : nat) (Hn : (2 <= n)%nat)
         (H2n : (1 < 2^n)%nat) (Hn2 : (0 < 2^(n-2))%nat),
    znz_units_group (2^n) H2n ≅
    znz_group (2^(n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1).
```

n ≥ 2 のとき (Z/2^nZ)* ≅ Z/2^(n-2)Z × Z/2Z。

## 数学的概要

生成元: 5（位数 2^(n-2)）と -1 ≡ 2^n-1（位数 2）。
同型写像 φ(a, b) = 5^a * (-1)^b mod 2^n。
両群の位数は 2^(n-1) = φ(2^n)。準同型・単射 → 全射（同位数）。

## Proof Strategy

1. φ : Z/2^(n-2)Z × Z/2Z → (Z/2^nZ)* を具体的に構成。
2. φ の準同型性: 指数の加算と乗算の対応（Z.mul_mod 等）。
3. φ の単射性:
   - b=1 なら 5^a ≡ -1 (mod 2^n)。5^a ≡ 1 (mod 4) だが -1 ≡ 3 (mod 4)。矛盾。
   - b=0, 5^a ≡ 1 (mod 2^n) → 鍵補題 five_pow_two_k_congr により a=0。
4. φ の全射性: 両群が同じ位数 2^(n-1) を持つので単射 → 全射。

## Proposed Lemmas

### Phase 0: 算術基本事実
- [ ] `two_pow_ge2_gt_one`: ∀ n ≥ 2, 1 < 2^n
- [ ] `two_pow_nm2_pos`: ∀ n ≥ 2, 0 < 2^(n-2)
- [ ] `euler_phi_two_pow`: ∀ n ≥ 1, euler_phi(2^n) = 2^(n-1) [euler_phi_prime_pow 使用]
- [ ] `znz_units_pow2_order`: GroupOrder (znz_units_group (2^n) _) (2^(n-1))
- [ ] `znz_group_order_n`: GroupOrder (znz_group n Hn) n [Fin.t n との直接全単射]
- [ ] `inj_hom_equal_order_surj`: G ≅ (inj hom) H, |G|=|H| → surj [pigeonhole_Fin 系]

### Phase 1: 単位元判定
- [ ] `five_gcd_pow2`: Z.gcd 5 (Z.of_nat (2^n)) = 1 for n ≥ 1
- [ ] `neg_one_gcd_pow2`: Z.gcd (Z.of_nat (2^n) - 1) (Z.of_nat (2^n)) = 1 for n ≥ 2
- [ ] `five_pow_mod_four`: ∀ s : nat, (5^s) mod 4 = 1 [帰納法]

### Phase 2: 鍵合同式
- [ ] `one_plus_pow2_r_pow_s`: ∀ r ≥ 1, ∀ s : nat, (1+2^r)^s ≡ 1+s*2^r (mod 2^(r+1))
- [ ] `congr_pow_mod`: a ≡ b (mod m) → a^s ≡ b^s (mod m) for nat s
- [ ] `five_pow_two_k_congr`: ∀ k : nat, 5^(2^k) ≡ 1+2^(k+2) (mod 2^(k+3)) [k の帰納法]
- [ ] `five_pow_2k_s_congr`: ∀ k s : nat, 5^(2^k * s) ≡ 1+s*2^(k+2) (mod 2^(k+3))

### Phase 3: 5 の位数証明
- [ ] `five_pow_pow2_nm2_one`: ∀ n ≥ 2, 5^(2^(n-2)) ≡ 1 (mod 2^n) [P2-3, k=n-2]
- [ ] `nat_pow2_odd_decomp`: ∀ s > 0, ∃ k t, s = 2^k * t ∧ Odd t [nat の2進分解]
- [ ] `odd_mul_pow2_not_zero_mod`: ∀ r : nat, ∀ s : nat, Odd s → s * 2^r mod 2^(r+1) ≠ 0
- [ ] `five_pow_not_one_before`: ∀ n ≥ 3, ∀ s, 0 < s < 2^(n-2) → 5^s ≢ 1 (mod 2^n)

### Phase 4: -1 の位数
- [ ] `neg_one_sq_one_pow2`: ∀ n ≥ 2, (2^n-1)^2 ≡ 1 (mod 2^n)
- [ ] `neg_one_ne_one_pow2`: ∀ n ≥ 2, (2^n-1) mod 2^n ≠ 1

### Phase 5: 同型写像と主定理
- [ ] `phi_map`: φ の定義と型付け
- [ ] `phi_hom`: φ は群準同型
- [ ] `phi_inj`: φ は単射 [P1, P3, P4 を使用]
- [ ] `znz_units_pow2_structure`: 主定理 [φ の全単射性 + IsIsomorphism]

## Proof Order

1. `two_pow_ge2_gt_one`
2. `two_pow_nm2_pos`
3. `euler_phi_two_pow`
4. `znz_units_pow2_order`
5. `znz_group_order_n`
6. `inj_hom_equal_order_surj`
7. `five_gcd_pow2`
8. `neg_one_gcd_pow2`
9. `five_pow_mod_four`
10. `one_plus_pow2_r_pow_s`
11. `congr_pow_mod`
12. `five_pow_two_k_congr` ← 核心
13. `five_pow_2k_s_congr`
14. `five_pow_pow2_nm2_one`
15. `nat_pow2_odd_decomp`
16. `odd_mul_pow2_not_zero_mod`
17. `five_pow_not_one_before`
18. `neg_one_sq_one_pow2`
19. `neg_one_ne_one_pow2`
20. `phi_map` / `phi_hom` / `phi_inj`
21. `znz_units_pow2_structure`
