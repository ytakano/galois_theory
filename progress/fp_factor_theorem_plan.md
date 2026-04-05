# Proof Plan: fp_factor_theorem (Fp上の因数定理)

## Goal

Fp 係数の多項式 f(x) に対して、以下は同値:
1. f(x) が (x-a) で割り切れる (poly_divides_linear)
2. f(a) = 0
3. a が f(x) = 0 の解

具体的に証明すべき主定理:
```coq
Theorem factor_theorem :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_divides_linear F f a <-> poly_eval F f a = ring_zero F.
```

および Fp への特殊化:
```coq
Corollary fp_factor_theorem :
  forall (p : nat) (Hp : prime (Z.of_nat p))
         (f : list (ring_carrier (znz_p_field p Hp)))
         (a : ring_carrier (znz_p_field p Hp)),
    poly_divides_linear (znz_p_field p Hp) f a <->
    poly_eval (znz_p_field p Hp) f a = ring_zero (znz_p_field p Hp).
```

## Proof Strategy

`poly_remainder_theorem`（証明済み）を基盤とする:
- f(x) = (x-a)*q(x) + f(a)   [poly_remainder_theorem]

(→): f(a) = 0 ならば f(x) = (x-a)*q(x)、商は poly_synthetic_div F f a
(←): ∃ q, f(x) = (x-a)*q(x) ならば x=a を代入して f(a) = 0*q(a) = 0

## Proposed Lemmas

- [ ] `poly_divides_linear` (定義): ∃ q, ∀ x, f(x) = (x-a)*q(x)
- [ ] `poly_factor_of_root`: f(a) = 0 → poly_divides_linear F f a
- [ ] `poly_root_of_factor`: poly_divides_linear F f a → f(a) = 0
- [ ] `factor_theorem`: 双条件（主定理）
- [ ] `fp_factor_theorem`: Fp への系

## Proof Order

1. `poly_divides_linear` (定義)
2. `poly_factor_of_root`
3. `poly_root_of_factor`
4. `factor_theorem`
5. `fp_factor_theorem`

## Dependencies

- `poly_remainder_theorem` (既証明)
- `ring_add_zero_r` (既証明)
- `ring_add_neg_r` (既証明): a + (-a) = 0
- `ring_mul_zero_l` (既証明): 0 * a = 0
