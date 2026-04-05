# Proof Plan: Field (体) の定義

## Goal

`integer.v` に環 (Ring) と体 (Field) の Record 定義を追加し、
基本補題を証明する。具体例として Z/pZ (p は素数) が体であることを示す。

## Proof Strategy

Ring → Field の階層で定義する。
- Ring: 加法可換群 + 乗法モノイド + 分配法則
- Field: 可換環 + 非零元の乗法逆元

## Proposed Lemmas / Definitions

- [ ] `Ring` Record: carrier, add, zero, neg, mul, one + 11 公理
- [ ] `ring_add_zero_r`: a + 0 = a
- [ ] `ring_add_neg_r`: a + (-a) = 0
- [ ] `ring_mul_zero_l`: 0 * a = 0
- [ ] `ring_mul_zero_r`: a * 0 = 0
- [ ] `ring_neg_neg`: -(-a) = a
- [ ] `ring_add_cancel_l`: a+b = a+c → b = c
- [ ] `ring_neg_mul_l`: (-a) * b = -(a * b)
- [ ] `ring_neg_mul_r`: a * (-b) = -(a * b)
- [ ] `Field` Record: field_ring :> Ring + field_inv + field_mul_comm + field_inv_l + field_one_ne_zero
- [ ] `field_inv_r`: x ≠ 0 → x * inv x = 1
- [ ] `field_inv_nonzero`: x ≠ 0 → inv x ≠ 0
- [ ] `field_no_zero_divisors`: a * b = 0 → a = 0 ∨ b = 0
- [ ] `field_mul_cancel_l`: a ≠ 0 → a*b = a*c → b = c
- [ ] `field_div`: 除法の定義 a / b := a * inv b
- [ ] `znz_p_field`: Z/pZ は素数 p に対して体

## Proof Order

1. `Ring` Record
2. `ring_add_zero_r`
3. `ring_add_neg_r`
4. `ring_mul_zero_l`
5. `ring_mul_zero_r`
6. `ring_neg_neg`
7. `ring_add_cancel_l`
8. `ring_neg_mul_l`
9. `ring_neg_mul_r`
10. `Field` Record
11. `field_inv_r`
12. `field_inv_nonzero`
13. `field_no_zero_divisors`
14. `field_mul_cancel_l`
15. `field_div`
16. `znz_p_field`
