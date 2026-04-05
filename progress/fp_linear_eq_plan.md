# Proof Plan: fp_linear_eq_unique_solution

## Goal

体 F 上の1次方程式 `ax + b = 0` が `a ≠ 0` のとき、ちょうど1つの解を持つことを証明する。

主定理 (抽象 Field レベル):
```coq
Theorem field_linear_eq_unique_solution : forall (F : Field) (a b : ring_carrier F),
  a <> ring_zero F ->
  exists! x : ring_carrier F,
    ring_add F (ring_mul F a x) b = ring_zero F.
```

系 (Fp への特化):
```coq
Corollary fp_linear_eq_unique_solution : forall (p : nat) (Hp : prime (Z.of_nat p))
    (a b : ring_carrier (znz_p_field p Hp)),
  a <> ring_zero (znz_p_field p Hp) ->
  exists! x : ring_carrier (znz_p_field p Hp),
    ring_add (znz_p_field p Hp) (ring_mul (znz_p_field p Hp) a x) b =
    ring_zero (znz_p_field p Hp).
```

## Proof Strategy

1. 解 x₀ = -(inv(a) * b) が方程式を満たすことを示す (存在)
2. 2つの解は一致することを示す (一意性)
3. `exists!` で組み合わせる

## Proposed Lemmas

- [ ] `field_linear_eq_solution`: x₀ = -(inv(a)*b) が a*x₀+b=0 を満たす
- [ ] `field_linear_eq_unique`: 2つの解が等しい
- [ ] `field_linear_eq_unique_solution`: 主定理 (exists!)
- [ ] `fp_linear_eq_unique_solution`: Fp への系

## Proof Order

1. `field_linear_eq_solution`
   - x₀ := -(inv(a) * b)
   - a * (-(inv(a) * b)) + b
     = -(a * (inv(a) * b)) + b    (ring_neg_mul_l)
     = -((a * inv(a)) * b) + b    (ring_mul_assoc)
     = -(1 * b) + b               (field_inv_r)
     = -b + b                     (ring_mul_one_l)
     = 0                          (ring_add_neg_l)

2. `field_linear_eq_unique`
   - a*x + b = 0 かつ a*y + b = 0
   - 両辺から b を加法キャンセル: a*x = a*y (ring_add_cancel_l)
   - 両辺に inv(a) を左掛け (field_mul_cancel_l): x = y

3. `field_linear_eq_unique_solution`
   - exists x₀ = -(inv(a)*b)
   - split: 存在は field_linear_eq_solution、一意性は field_linear_eq_unique

4. `fp_linear_eq_unique_solution`
   - field_linear_eq_unique_solution を znz_p_field p Hp に適用
