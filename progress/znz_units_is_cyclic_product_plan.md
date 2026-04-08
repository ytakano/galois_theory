# Proof Plan: znz_units_is_cyclic_product

## Goal

```coq
(* 帰納的述語: G が巡回群の直積である *)
Inductive IsCyclicProduct : Group -> Prop :=
  | ICP_cyclic  : forall C : CyclicGroup, IsCyclicProduct C
  | ICP_product : forall G H : Group,
      IsCyclicProduct G -> IsCyclicProduct H ->
      IsCyclicProduct (G ×ₒ H)
  | ICP_iso     : forall G H : Group,
      G ≅ H -> IsCyclicProduct H -> IsCyclicProduct G.

(* 主定理: すべての n > 1 に対して (Z/nZ)* は巡回群の直積 *)
Theorem znz_units_is_cyclic_product :
  forall (n : nat) (Hn : (1 < n)%nat),
    IsCyclicProduct (znz_units_group n Hn).
```

## Proof Strategy

強帰納法 (strong induction on n) + 素数冪の場合分け:
1. n の最小素因数 p を Z.prime_divisor_exists で取得
2. p進付値 k = p_adic_val p n を計算
3. m = n / p^k として n = m * p^k, gcd(m, p^k) = 1
4. m = 1 の場合: n = p^k → 素数冪補題適用
5. m > 1 の場合: znz_units_decomp2 + 帰納仮定(m < n) + 素数冪補題

## Proposed Lemmas

### Phase 1: IsCyclicProduct 基本性質
- [x] `IsCyclicProduct` — 帰納的述語の定義 (ICP_cyclic, ICP_product, ICP_iso)
- [x] `icp_znz_group` — znz_group n Hn は IsCyclicProduct

### Phase 2: p=2 の場合
- [ ] `znz_units_2_order` — GroupOrder (znz_units_group 2 _) 1
- [ ] `group_order_1_is_cyclic` — 位数1の群は IsCyclicProduct
- [ ] `znz_units_pow2_is_cyclic_product` — (Z/2^kZ)* は IsCyclicProduct (k≥1)

### Phase 3: 奇素数冪
- [ ] `znz_units_odd_prime_pow_is_cyclic_product` — (Z/p^kZ)* は IsCyclicProduct (奇素数 p, k≥1)
- [ ] `znz_units_prime_pow_is_cyclic_product` — 任意の素数冪

### Phase 4: 数論インフラ
- [x] `nat_prime_divisor_exists` — n > 1 の素因数の存在
#- [x] `prime_divides_exists_prime_power_split` — p | n から n = m*p^


### Phase 5: 主定理
- [x] `znz_units_is_cyclic_product` — 強帰納法で主定理 (PROVED 2026-04-08)

## Proof Order

1. `IsCyclicProduct` (Definition) ✓
2. `icp_znz_group` ✓
3. `znz_units_2_order` ✓
4. `group_order_1_is_cyclic` ✓
5. `znz_units_pow2_is_cyclic_product` 
6. `znz_units_odd_prime_pow_is_cyclic_product` ✓
7. `znz_units_prime_pow_is_cyclic_product` ✓
8. `nat_prime_divisor_exists` ✓
9. `prime_divides_exists_prime_power_split` ✓
10. `znz_units_is_cyclic_product` (main) ✓

## 完了 (2026-04-08)
