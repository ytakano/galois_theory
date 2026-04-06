# Proof Plan: primitive_root_exists

## Goal

For any prime p, there exists a primitive root modulo p —
an element g ∈ (Z/pZ)* of order p-1.

```coq
Theorem primitive_root_exists :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p)),
    exists g : carrier (znz_units_group p Hp),
      mult_order_p p Hp Hprime g = (p - 1)%nat.
```

## Proof Strategy

Use the divisor counting argument:

For each d | (p-1), let ψ(d) = #{a ∈ (Z/pZ)* : ord(a) = d}.

1. ψ(d) ≤ φ(d) for all d | (p-1)  [polynomial bound + structure of cyclic order-d elements]
2. ∑_{d|(p-1)} ψ(d) = p-1           [Fermat + all orders divide p-1]
3. ∑_{d|(p-1)} φ(d) = p-1           [Euler divisor sum identity]

From 1+2+3: ψ(p-1) = φ(p-1) ≥ 1 → primitive root exists.

## Proposed Lemmas

### Phase 1: Fermat's Little Theorem
- [ ] `group_elements_list`: GroupOrder G n → ∃ L, NoDup L ∧ length L = n ∧ ∀x, In x L
- [ ] `znz_units_op_comm`: commutativity of znz_units_group (uses Z.mul_comm)
- [ ] `fold_right_mul_left_abelian`: fold_right (map (op a) L) = a^n * fold_right L [abelian]
- [ ] `znz_units_mul_left_permutation`: map (op a) L is a Permutation of L
- [ ] `fold_right_permutation_abelian`: Permutation → fold_right equal [abelian]
- [ ] `fermat_little_theorem`: a^(p-1) = 1 in (Z/pZ)*
- [ ] `mult_order_p_divides_p_minus_1`: mult_order_p a | (p-1)

### Phase 2: Polynomial Root Analysis
- [ ] `order_of_power_gcd`: ord(a^k) = ord(a) / gcd(k, ord(a))
- [ ] `order_d_elements_are_powers`: if ord(a)=d, then ∀x, x^d=1 → ∃k<d, a^k=x
  (uses fp_poly_roots_bound)

### Phase 3: Euler Divisor Sum
- [ ] `divisors_list`: list of all divisors of n
- [ ] `sum_phi_over_divisors`: ∑_{d|n} φ(d) = n

### Phase 4: Counting Argument
- [ ] `count_by_order_sum`: ∑_{d|(p-1)} ψ(d) = p-1
- [ ] `psi_le_phi_all`: ψ(d) ≤ φ(d) for all d | (p-1)
- [ ] `psi_eq_phi_all`: ψ(d) = φ(d) for all d | (p-1)
- [ ] `euler_phi_pos`: n ≥ 1 → φ(n) ≥ 1
- [ ] `primitive_root_exists` (main goal)

## Proof Order

1. `group_elements_list`
2. `znz_units_op_comm`
3. `fold_right_mul_left_abelian`
4. `znz_units_mul_left_permutation`
5. `fold_right_permutation_abelian`
6. `fermat_little_theorem`
7. `mult_order_p_divides_p_minus_1`
8. `order_of_power_gcd`
9. `order_d_elements_are_powers`
10. `divisors_list`
11. `sum_phi_over_divisors`
12. `count_by_order_sum`
13. `psi_le_phi_all`
14. `psi_eq_phi_all`
15. `euler_phi_pos`
16. `primitive_root_exists`
