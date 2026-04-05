# Proof Plan: mult_order (乗法位数)

## Goal

素数 p と a ≠ 0 (mod p) に対して、**乗法位数 ord_p(a)** を形式化する。

まず有限群の任意の元に対する「元の位数 (element order)」を定義し、その性質を証明する。
その後 `znz_units_group p Hp` ((Z/pZ)*) に適用して乗法位数を定義する。

### 主要定理

**(定理1)** `a^0, a^1, ..., a^(ord_p(a)-1)` はすべて異なる
**(定理2)** `a^x = e (mod p) ↔ ord_p(a) | x`

## Proof Strategy

### フェーズ1: 一般有限群の元の位数
1. 任意の有限群元 a は有限の周期を持つ（鳩ノ巣原理）
2. 最小周期 = 元の位数を `epsilon` で定義
3. `epsilon_spec` + `well_ordering_nat` で仕様証明

### フェーズ2: 主要性質
1. 周期キャンセル補題: `a^d = e → a^(d*k+r) = a^r`
2. 定理2: `a^x = e ↔ ord | x`（除算のアルゴリズムを使う）
3. 定理1: `a^i = a^j (i,j < ord, i≠j)` から矛盾を導く

### フェーズ3: Fp* への適用
1. `euler_phi p = p-1` for prime p（`euler_phi_prime_pow` を使用）
2. `GroupOrder (Z/pZ)* (p-1)` for prime p
3. 乗法位数の定義と定理1・2の系

## Proposed Lemmas

### フェーズ1
- [ ] `element_has_finite_period`: `GroupOrder G m → ∃ d>0, gpow G a (Z.of_nat d) = e G`
- [ ] `mult_order_exists`: 最小周期の存在（well_ordering を使う）
- [ ] `mult_order`: 元の位数の定義（`epsilon`）
- [ ] `mult_order_spec`: 仕様補題（pos, pow = e, minimality）

### フェーズ2
- [ ] `gpow_nat_period_cancel`: `gpow_nat G a d = e G → gpow_nat G a (d*k+r) = gpow_nat G a r`
- [ ] `mult_order_divides`: 定理2 `gpow_nat G a x = e G ↔ (mult_order | x)`
- [ ] `mult_order_powers_distinct`: 定理1 `i,j < ord, i≠j → a^i ≠ a^j`

### フェーズ3
- [ ] `euler_phi_prime`: `prime (Z.of_nat p) → euler_phi p = p-1`
- [ ] `prime_units_group_order`: `GroupOrder (znz_units_group p Hp) (p-1)` for prime p
- [ ] `mult_order_p`: 乗法位数 `mult_order_p p Hp Hprime a` の定義
- [ ] `mult_order_p_powers_distinct`: 定理1の系
- [ ] `mult_order_p_divides`: 定理2の系

## Proof Order

1. `element_has_finite_period`
2. `mult_order_exists`
3. `mult_order` (Definition)
4. `mult_order_spec`
5. `gpow_nat_period_cancel`
6. `mult_order_divides` (定理2)
7. `mult_order_powers_distinct` (定理1)
8. `euler_phi_prime`
9. `prime_units_group_order`
10. `mult_order_p` (Definition)
11. `mult_order_p_powers_distinct`
12. `mult_order_p_divides`

## 依存する既存補題

| 補題 | 用途 |
|------|------|
| `pigeonhole_Fin` | 有限群元の有限周期性の証明 |
| `equal_powers_imply_period` | `a^i = a^j → a^(j-i) = e` |
| `gpow_of_nat` | `gpow G a (Z.of_nat k) = gpow_nat G a k` |
| `well_ordering_nat` | 最小周期の存在 |
| `group_order_pos` | GroupOrder から位数が正 |
| `gpow_nat_add` | `a^(m+n) = a^m * a^n` |
| `gpow_nat_mul` | `a^(m*n) = (a^m)^n` |
| `gpow_nat_e` | `e^n = e` |
| `id_left` | `e * a = a` |
| `epsilon` / `epsilon_spec` | 選択関数 |
| `euler_phi_prime_pow` | `euler_phi(p^e) = p^(e-1)*(p-1)` |
| `euler_phi_group_order` | `GroupOrder (znz_units_group n Hn) (euler_phi n)` |
