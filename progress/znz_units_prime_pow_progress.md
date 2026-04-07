# Proof Progress: znz_units_prime_pow_structure / cyclic

## Status Overview
- Overall: In Progress
- Complete Lemmas: 23/26+ (Phase 0 + Phase 1 + Phase 2 complete)
- Unproven (`Admitted`): Phase 3-4 lemmas still needed
- Failed/Abandoned Items: none

## Completed Lemmas

### Phase 0 (complete)
- `GroupIsomorphic_trans`: transitivity of ≅
- `odd_prime_pow_gt_one`: (1 < p) → (1 ≤ n) → (1 < p^n)
- `odd_prime_pow_units_order`: GroupOrder (znz_units_group (p^n) _) (p^(n-1)*(p-1))

### Phase 1 (complete — 2026-04-08)
- `geom_sum`: Fixpoint definition, sum_{i=0}^{n-1} A^i
- `geom_sum_spec`: (A-1) * geom_sum A n = A^n - 1
- `geom_sum_split`: geom_sum A (p*N) = geom_sum (A^N) p * geom_sum A N
- `sq_dvd_pow_minus_one_linear`: (A-1)^2 | A^i - 1 - i*(A-1)
- `geom_sum_dvd_p`: p | A-1 → p | geom_sum A p
- `one_plus_p_geom_sum_pk_dvd`: p^k | geom_sum (1+p) (p^k)
- `one_plus_p_pow_pk_dvd`: p^(k+1) | (1+p)^(p^k) - 1
- `nat_sum_below`: Fixpoint, sum_{i=0}^{n-1} i
- `nat_sum_below_double`: 2*T = p*(p-1)
- `nat_sum_below_dvd_odd_prime`: p | nat_sum_below p (odd prime)
- `geom_sum_sq_approx`: (A-1)^2 | geom_sum A p - p - (A-1)*T
- `geom_sum_not_dvd_p_sq`: p^2 ∤ geom_sum ((1+p)^(p^k)) p (odd prime)
- `one_plus_p_pow_pk_not_dvd`: p^(k+2) ∤ (1+p)^(p^k) - 1 [COMPILED ✓]
- `znz_units_gpow_nat_val`: proj1_sig (gpow_nat G a k) = (proj1_sig a)^k mod n [COMPILED ✓]
- `one_plus_p_coprime_p`: gcd(1+p, p) = 1 [COMPILED ✓]
- `one_plus_p_coprime_pn`: gcd(1+p, p^n) = 1 [COMPILED ✓]
- `nat_prime_pow_divisors`: divisors of p^m are powers of p [COMPILED ✓]
- `one_plus_p_mult_order`: mult_order of (1+p) in (Z/p^nZ)* = p^(n-1) [COMPILED ✓]

### Phase 2 (complete — 2026-04-07)
- `znz_units_op_comm_gen`: op commutativity for znz_units_group n Hn (any n) [COMPILED ✓]
- `gpow_group_order_eq_e`: Lagrange theorem for abelian finite groups — gpow_nat G a m = e [COMPILED ✓]
- `order_of_power_gcd_general`: mult_order(g^k) = mult_order(g)/gcd(k, mult_order(g)) for any finite group G [COMPILED ✓]
- `pnm1_pm1_coprime`: gcd(p^(n-1), p-1) = 1 for odd prime p, n≥1 [COMPILED ✓]
- `lift_prim_root_to_pn`: ∃ g ∈ (Z/p^nZ)* of order p-1 [COMPILED ✓]

## TODO

### Phase 3: 同型写像
- [ ] `phi_hom_inj`: the map φ(a,b)=h^a·g^b is an injective homomorphism
- [ ] `znz_units_odd_prime_pow_structure` (THEOREM 1)

### Phase 4: 巡回性
- [ ] `znz_units_odd_prime_pow_cyclic` (THEOREM 2)
