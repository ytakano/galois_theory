# Proof Plan: (Z/p^nZ)* の構造定理と巡回性

## 問題

pを奇素数、n≥1 のとき:
- **定理1 (構造定理)**: (Z/p^nZ)* ≅ Z/p^(n-1)Z × Z/(p-1)Z
- **定理2 (巡回性)**: (Z/p^nZ)* は巡回群である（Z/φ(p^n)Z に同型）

## 難易度評価

**Complex** — 代数的整数論の核心定理。6つのフェーズに分解し、20以上の補題が必要。
先行実装 `znz_units_pow2_structure` (p=2 の場合) の構造を参考にする。

## 目標 Rocq 文

```coq
(* 定理1: 構造定理 *)
Theorem znz_units_odd_prime_pow_structure :
  forall (p n : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (Hodd : p <> 2) (Hn : (1 <= n)%nat) (Hpn : (1 < p^n)%nat),
    exists (Hpnm1 : (0 < p^(n-1))%nat) (Hpm1 : (0 < p-1)%nat),
      znz_units_group (p^n) Hpn ≅
      znz_group (p^(n-1)) Hpnm1 ×ₒ znz_group (p-1) Hpm1.

(* 定理2: 巡回性 *)
Theorem znz_units_odd_prime_pow_cyclic :
  forall (p n : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (Hodd : p <> 2) (Hn : (1 <= n)%nat) (Hpn : (1 < p^n)%nat),
    exists (Hphi : (0 < p^(n-1) * (p-1))%nat),
      znz_units_group (p^n) Hpn ≅ znz_group (p^(n-1) * (p-1)) Hphi.
```

## 既存コードの活用

| 既存定理/補題 | 用途 |
|---|---|
| `euler_phi_prime_pow` | φ(p^n) = p^(n-1)(p-1) |
| `euler_phi_group_order` | GroupOrder (znz_units_group p^n) (euler_phi p^n) |
| `primitive_root_exists` | Z/pZ に原始根が存在 |
| `znz_units_group_cyclic_iso` | (Z/pZ)* ≅ Z/(p-1)Z（n=1 ケース） |
| `cyclic_group_isomorphic_znz` | 位数 n の巡回群 ≅ Z/nZ |
| `group_order_product` | GroupOrder (G ×ₒ H) (m*n) |
| `inj_hom_surj_of_eq_order` | 単射準同型 + 同位数 → 全射（全単射） |
| `mult_order`, `mult_order_spec` | 元の位数の最小性 |
| `order_of_power_gcd` | 冪の位数（p 素数版; 一般化が必要） |
| `znz_units_pow2_structure` | p=2 の場合の構造定理（証明パターンの参考） |
| `five_pow_two_k_congr` / `five_pow_not_one_before` | 対応する 1+p 版の参考実装 |

---

## フェーズ分解

### Phase 0: 算術基礎補題

- **`odd_prime_pow_gt_one`**
  ```coq
  Lemma odd_prime_pow_gt_one :
    forall (p n : nat), (1 < p)%nat -> (1 <= n)%nat -> (1 < p^n)%nat.
  ```
  証明: `Nat.one_lt_pow` または `Nat.lt_le_trans` + `Nat.pow_lt_pow_r`。

- **`odd_prime_pos`**  
  pが奇素数 → `(0 < p-1)%nat`。`lia` で自明。

- **`odd_prime_pow_units_order`**
  ```coq
  Lemma odd_prime_pow_units_order :
    forall (p n : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
           (Hn : (1 <= n)%nat) (Hpn : (1 < p^n)%nat),
      GroupOrder (znz_units_group (p^n) Hpn) (p^(n-1) * (p-1)).
  ```
  証明: `euler_phi_group_order` + `euler_phi_prime_pow`。

---

### Phase 1: 1+p の位数

1+p が (Z/p^nZ)* の中で位数 p^(n-1) を持つことを示す。

- **`one_plus_p_coprime_pow`**
  ```coq
  Lemma one_plus_p_coprime_pow :
    forall (p n : nat), prime (Z.of_nat p) -> (1 <= n)%nat ->
      Z.gcd (1 + Z.of_nat p) (Z.of_nat (p^n)) = 1.
  ```
  証明: `prime_pow_coprime_iff` + `gcd(1+p, p) = 1` (素数 p は 1+p を割り切らない)。

- **`lte_odd_prime`** (Lifting the Exponent 補題の核心)
  ```coq
  Lemma one_plus_p_pow_pk_congr :
    forall (p k : nat), prime (Z.of_nat p) -> p <> 2 ->
      ((1 + Z.of_nat p)^(Z.of_nat (p^k)) - 1) mod Z.of_nat (p^(k+2)) = Z.of_nat (p^(k+1)) mod Z.of_nat (p^(k+2)).
  ```
  すなわち: (1+p)^(p^k) ≡ 1 + p^(k+1) (mod p^(k+2)) for all k ≥ 0。  
  証明方針（k の帰納法）:
  - 基底: k=0 → (1+p)^1 = 1+p ≡ 1+p (mod p^2) ✓
  - 帰納: IH より (1+p)^(p^k) = 1 + p^(k+1) + A·p^(k+2)。  
    これを p 乗すると二項展開で:  
    ((1+p)^(p^k))^p = (1 + p^(k+1) + A·p^(k+2))^p  
    = 1 + p·p^(k+1) + (p-valuation ≥ k+3 の項)  
    = 1 + p^(k+2) (mod p^(k+3))  
    **技術的課題**: 二項定理 `Nat.choose_add` または `Z.binomial_def` が必要。  
    Rocq 標準ライブラリに `Nat.choose` があるため `Z.binomial` 補題を構成する。  
    代替: 帰納法で直接計算し、`p | Nat.choose p j` (1 ≤ j ≤ p-1) を利用。

- **`prime_dvd_binom`**（技術的補題）
  ```coq
  Lemma prime_dvd_binom :
    forall (p j : nat), prime (Z.of_nat p) -> (1 <= j)%nat -> (j <= p-1)%nat ->
      (Z.of_nat p | Z.of_nat (Nat.choose p j)).
  ```
  証明: `prime (Z.of_nat p)` と `Nat.choose_sym`/`Nat.choose_mul` から。  
  Stdlib に `Nat.prime_dvd_choose` 相当があれば利用。

- **`one_plus_p_pow_pnm1_one`**
  ```coq
  Lemma one_plus_p_pow_pnm1_one :
    forall (p n : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
           (Hodd : p <> 2) (Hn : (2 <= n)%nat),
      (1 + Z.of_nat p)^(Z.of_nat (p^(n-1))) mod Z.of_nat (p^n) = 1.
  ```
  証明: `one_plus_p_pow_pk_congr` を k=n-2 で適用 → (1+p)^(p^(n-2+1)) = (1+p)^(p^(n-1)) ≡ 1 + p^n (mod p^(n+1)) なので mod p^n では 1 に合同。

- **`p_pow_decomp`**（p 進分解）
  ```coq
  Lemma p_pow_decomp :
    forall (p s : nat), prime (Z.of_nat p) -> (0 < s)%nat ->
      exists k t : nat, (s = p^k * t)%nat /\ ~ (p | t) /\ (0 < t)%nat.
  ```
  証明: s についての強帰納法（p で割り切れる場合を分解）。  
  `nat_pow2_odd_decomp` の p 版（p=2 版がすでに存在）。

- **`one_plus_p_pow_not_one_before`**
  ```coq
  Lemma one_plus_p_pow_not_one_before :
    forall (p n s : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
           (Hodd : p <> 2) (Hn : (2 <= n)%nat),
      (0 < s)%nat -> (s < p^(n-1))%nat ->
      (1 + Z.of_nat p)^(Z.of_nat s) mod Z.of_nat (p^n) <> 1.
  ```
  証明: `p_pow_decomp` で s = p^k * t (p ∤ t) と分解。  
  `one_plus_p_pow_pk_congr` より (1+p)^(p^k) ≡ 1 + p^(k+1) (mod p^(k+2))。  
  この LTE 的議論: v_p((1+p)^s - 1) = k+1 ≤ n-1 < n なので p^n ∤ (1+p)^s - 1。

- **`one_plus_p_mult_order`**
  ```coq
  Lemma one_plus_p_mult_order :
    forall (p n : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
           (Hodd : p <> 2) (Hn : (2 <= n)%nat) (Hpn : (1 < p^n)%nat),
      let h := exist _ ((1 + Z.of_nat p) mod Z.of_nat (p^n))
                       (...) : carrier (znz_units_group (p^n) Hpn) in
      mult_order (znz_units_group (p^n) Hpn) (p^(n-1) * (p-1))
                 (odd_prime_pow_units_order ...) h
      = p^(n-1).
  ```
  証明: `mult_order_spec` の最小性 + `one_plus_p_pow_pnm1_one` + `one_plus_p_pow_not_one_before`。

---

### Phase 2: p-1 位数の元の存在

(Z/p^nZ)* の中に位数ちょうど p-1 の元が存在することを示す。

- **`order_of_power_gcd_general`**（既存 `order_of_power_gcd` の一般化）
  ```coq
  Lemma order_of_power_gcd_general :
    forall (G : Group) (m : nat) (Hm : GroupOrder G m)
           (a : carrier G) (k : nat),
      mult_order G m Hm (gpow_nat G a k) =
      Nat.div (mult_order G m Hm a) (Nat.gcd k (mult_order G m Hm a)).
  ```
  証明: `order_of_power_gcd` の証明を `G` 一般に移植（`mult_order_p_pow_is_e` → `mult_order_spec` の適用）。

- **`lift_elem_to_pn`**
  ```coq
  Lemma lift_elem_to_pn :
    forall (p n : nat) (Hp : (1 < p)%nat) (Hpn : (1 < p^n)%nat) (a : Z),
      0 <= a < Z.of_nat p ->
      Z.gcd a (Z.of_nat p) = 1 ->
      exists b : carrier (znz_units_group (p^n) Hpn),
        proj1_sig b mod Z.of_nat p = a mod Z.of_nat p.
  ```
  証明: `a mod p^n` は `a < p < p^n` なので `a` 自体が carrier。
  `gcd(a, p^n) = 1` は `prime_pow_coprime_iff` + `gcd(a, p) = 1` から。

- **`order_pm1_exists_in_pn_units`**
  ```coq
  Lemma order_pm1_exists_in_pn_units :
    forall (p n : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
           (Hodd : p <> 2) (Hn : (1 <= n)%nat) (Hpn : (1 < p^n)%nat),
      exists g : carrier (znz_units_group (p^n) Hpn),
        mult_order (znz_units_group (p^n) Hpn) (p^(n-1)*(p-1))
                   (odd_prime_pow_units_order ...) g
        = (p - 1)%nat.
  ```
  証明戦略:
  1. `primitive_root_exists` で g₀ ∈ (Z/pZ)* を得る（位数 p-1）
  2. `lift_elem_to_pn` で G ∈ (Z/p^nZ)* を構成（G ≡ g₀ mod p）
  3. G の位数 d は p^(n-1)(p-1) を割り、(p-1) | d
     （Gmod p の位数が d を割り、Gmod p の位数 = p-1 なので (p-1)|d）
  4. d = p^k(p-1) と書けるので G^(p^k) の位数は
     `order_of_power_gcd_general` より d/gcd(p^k, d) = p^(n-1)(p-1)/(p^k · p^(k)?…
     
     正確には: d | p^(n-1)(p-1)、(p-1)|d。
     d を p^(n-1)(p-1) の因子で (p-1) の倍数のものとして書くと d = p^k(p-1) (0≤k≤n-1)。
     G^(p^k) の位数 = d/gcd(p^k, d) = p^k(p-1)/gcd(p^k, p^k(p-1)) = p^k(p-1)/p^k = p-1 ✓

---

### Phase 3: 互素性と積群の巡回性

- **`pnm1_pm1_coprime`**
  ```coq
  Lemma pnm1_pm1_coprime :
    forall (p n : nat), prime (Z.of_nat p) -> p <> 2 -> (1 <= n)%nat ->
      Nat.gcd (p^(n-1)) (p-1) = 1.
  ```
  証明: p は奇素数 → p ∤ (p-1)（p-1 < p なので）。
  したがって p も p^(n-1) のどの素因子も (p-1) を割り切らない。
  `Nat.gcd_eq_one` か `rel_prime` + `prime_pow_coprime_iff`。

- **`znz_product_isomorphic_to_product`**（位数 mn の znz_group を Z/mZ × Z/nZ に分解）  
  Already: `znz_decomp` が存在するが units 群ではなくそのまま使えるか要確認。  
  もし使えない場合:
  ```coq
  Lemma znz_group_product_if_coprime :
    forall (m n : nat) (Hm : (0 < m)%nat) (Hn : (0 < n)%nat)
           (Hmn : (0 < m*n)%nat) (Hcop : Nat.gcd m n = 1),
      znz_group (m*n) Hmn ≅ znz_group m Hm ×ₒ znz_group n Hn.
  ```
  証明: `znz_decomp`（2変数版 CRT）を利用。すでに `znz_decomp` 定理が存在。

---

### Phase 4: 同型写像の構成（定理1）

1+p の生成する部分群（位数 p^(n-1)）と g の生成する部分群（位数 p-1）が
直積分解を与えることを具体的に構成する。

- **`phi_def`**: 写像 φ(a, b) = h^a · g^b mod p^n の定義  
  h = (1+p mod p^n) ∈ (Z/p^nZ)*、g = 上で得た位数 p-1 の元  
  a ∈ Z/p^(n-1)Z（0≤a<p^(n-1)）、b ∈ Z/(p-1)Z（0≤b<p-1）

- **`phi_hom`**: φ は群準同型  
  φ(a₁+a₂, b₁+b₂) = h^(a₁+a₂) · g^(b₁+b₂) = h^a₁ g^b₁ · h^a₂ g^b₂  
  （h と g が可換であることが必要 → `znz_units_op_comm` で OK、アーベル群）

- **`phi_inj`**: φ は単射  
  φ(a₁,b₁) = φ(a₂,b₂) → h^a₁ g^b₁ = h^a₂ g^b₂ → h^(a₁-a₂) = g^(b₂-b₁)  
  左辺の位数は p^(n-1) を割り、右辺の位数は (p-1) を割る。  
  互素性 `pnm1_pm1_coprime` → 両辺 = e → a₁=a₂, b₁=b₂。

- **`phi_surj`**: 単射 + 同位数（`inj_hom_surj_of_eq_order`）→ 全射

- **`znz_units_odd_prime_pow_structure`**: 主定理  
  φ が Z/p^(n-1)Z × Z/(p-1)Z → (Z/p^nZ)* の同型。

---

### Phase 5: 巡回性（定理2）

- **`znz_units_odd_prime_pow_cyclic`**:  
  定理1より (Z/p^nZ)* ≅ Z/p^(n-1)Z × Z/(p-1)Z。  
  `pnm1_pm1_coprime` + `znz_group_product_if_coprime` より  
  Z/p^(n-1)Z × Z/(p-1)Z ≅ Z/(p^(n-1)(p-1))Z = Z/φ(p^n)Z。  
  推移律 `GroupIsomorphic_trans`（存在するか要確認; なければ証明する）で合成。

---

## 補題の証明順序

```
Phase 0:
1.  odd_prime_pow_gt_one
2.  odd_prime_pos
3.  odd_prime_pow_units_order

Phase 1: 1+p の位数
4.  one_plus_p_coprime_pow
5.  prime_dvd_binom
6.  one_plus_p_pow_pk_congr         ← 核心1（二項定理 + 帰納法）
7.  one_plus_p_pow_pnm1_one
8.  p_pow_decomp
9.  one_plus_p_pow_not_one_before    ← 核心2（LTE 的議論）
10. one_plus_p_mult_order

Phase 2: p-1 位数の元の存在
11. order_of_power_gcd_general
12. lift_elem_to_pn
13. order_pm1_exists_in_pn_units     ← 核心3（リフティング）

Phase 3: 互素性
14. pnm1_pm1_coprime
15. znz_group_product_if_coprime     （必要なら）

Phase 4: 同型写像
16. phi_def / phi_hom
17. phi_inj
18. phi_surj
19. znz_units_odd_prime_pow_structure（定理1）

Phase 5: 巡回性
20. GroupIsomorphic_trans            （必要なら）
21. znz_units_odd_prime_pow_cyclic   （定理2）
```

---

## 技術的注意点

1. **二項定理の Rocq 表現**: Rocq 標準ライブラリに `Nat.choose` はあるが、Z 上の二項展開補題は限定的。  
   `prime_dvd_binom` には `Znumtheory` の `prime_dvd_binomial` か手動証明が必要。  
   代替: `one_plus_p_pow_pk_congr` の証明を二項定理を使わずに直接計算で行う  
   （`one_plus_p_pow_pk_congr` を mod の等式として直接 Z 計算で示す）。

2. **`znz_units_pow2_structure` との類似**: p=2 版の証明パターン  
   (`five_pow_two_k_congr`, `five_pow_not_one_before`, `phi_inj` での mod 4 議論)  
   を odd prime 版に一般化する際の参考とする。  
   ただし odd prime 版では mod 4 → mod p の議論に切り替える。

3. **`phi_inj` の互素性議論**: (Z/p^nZ)* はアーベル群なので h と g は可換。  
   h^(a1-a2) = g^(b2-b1) から両辺の位数の互素性で = e を導く。  
   具体的には: 左辺の p^(n-1) 乗 = e → 右辺の p^(n-1) 乗 = e。  
   (p-1)|p^(n-1) でない（互素）ので右辺自体 = e。

4. **n=1 の特殊ケース**: n=1 のとき (Z/pZ)* ≅ Z/1Z × Z/(p-1)Z ≅ Z/(p-1)Z。  
   Phase 1 の `one_plus_p_pow_pnm1_one` で n=1 → p^(n-1) = p^0 = 1 なので  
   (1+p)^1 mod p^1 = (1+p) mod p = 1 ✓。  
   Phase 2 は n=1 のとき 位数 p-1 の元 = primitive_root 自身（既存定理を使う）。  
   統一的に扱えるが、n=1 の場合は `znz_units_group_cyclic_iso` を直接使うことも可。

5. **progress ファイル**: 
   - `progress/znz_units_prime_pow_plan.md` — このファイルの copy
   - `progress/znz_units_prime_pow_progress.md` — 実装時に作成

---

## 利用する標準ライブラリ補題（追加分）

| 補題候補 | 用途 |
|---|---|
| `Nat.prime_dvd_choose` / `Z.prime_dvd_binomial` | prime_dvd_binom |
| `Z.pow_mod` | mod の冪計算 |
| `Z.mul_pow` | 冪の乗法則 |
| `Nat.gcd_pow_l` or `Z.coprime_pow_r` | pnm1_pm1_coprime |
| `Nat.div_mul_cancel` | order_of_power_gcd_general |
| `Z.gauss` | phi_inj での互素性議論 |
