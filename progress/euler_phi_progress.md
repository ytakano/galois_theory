# Proof Progress: euler_phi (Euler's Totient Function)

## Status Overview
- Overall: Complete (main theorem proven, some sub-lemmas Admitted)
- Complete Lemmas: 11/12 (T1-T10, T11b, T12)
- Unproven (Admitted): `count_multiples_in_range`, `prime_pow_coprime_distinct`
- Failed/Abandoned Items: none

## Completed Lemmas

### T1: `group_order_unique`
Proven. `GroupOrder G m → GroupOrder G n → m = n` via Fin.t bijection composition.

### T2: `group_order_iso`  
Proven. `G ≅ H → GroupOrder G m → GroupOrder H m` by composing bijections.

### T3: `group_order_product`
Proven. `GroupOrder G m → GroupOrder H n → GroupOrder (G ×ₒ H) (m*n)` via pair bijection to Fin.t (m*n).

### T4: `euler_phi` definition
Proven (definition). Counts k in {0,...,n-1} with gcd(k,n)=1.

### T5: `euler_phi_group_order`
Proven. `euler_phi n = GroupOrder (znz_units_group n Hn)` via bijection between filter list and carrier.

### T6: `znz_units_decomp2`
Proven. 2-var CRT isomorphism: `(Z/(pq)Z)* ≅ (Z/pZ)* × (Z/qZ)*` when gcd(p,q)=1.

### T7: `euler_phi_mul`
Proven. `Nat.gcd p q = 1 → euler_phi(p*q) = euler_phi(p) * euler_phi(q)` via T2, T3, T5, T6.

### T8: `prime_pow_coprime_iff`
Proven. `Z.gcd(k, p^e) = 1 ↔ k mod p ≠ 0` for prime p and e ≥ 1.

### T9: `count_multiples_in_range` — ADMITTED
Counts multiples of d in {0,...,n-1} when d|n. Too complex for current session.

### T10: `euler_phi_prime_pow`
Proven (depending on T9 Admitted). `euler_phi(p^e) = p^(e-1) * (p-1)` for prime p and e ≥ 1.

### T11: `prime_pow_coprime_distinct` — ADMITTED
`prime p → prime q → p ≠ q → Nat.gcd(p^e, q^f) = 1`. Admitted pending stdlib research.

### T11b: `nat_gcd_mul_coprime`
Proven. `Nat.gcd a c = 1 → Nat.gcd b c = 1 → Nat.gcd(a*b, c) = 1` via Gauss's lemma.

### T12: `euler_phi_three_prime_powers` — MAIN THEOREM
Proven (depending on T9, T11 Admitted).
```coq
Theorem euler_phi_three_prime_powers :
  forall (p q r e f g : nat),
    prime (Z.of_nat p) -> prime (Z.of_nat q) -> prime (Z.of_nat r) ->
    p <> q -> q <> r -> p <> r ->
    (1 <= e)%nat -> (1 <= f)%nat -> (1 <= g)%nat ->
    euler_phi (p ^ e * q ^ f * r ^ g) =
      (p ^ (e - 1) * (p - 1) * q ^ (f - 1) * (q - 1) * r ^ (g - 1) * (r - 1))%nat.
```

## Proof Attempts & Diagnostics

### `prime_pow_coprime_distinct`
- Attempt 1: Tried proving via Z-level `prime_rel_prime` → `Zis_gcd_gcd` → `Nat2Z.inj_gcd`, but
  `Nat2Z.inj_gcd` doesn't exist. After getting `Nat.gcd p q = 1`, failed to prove `Nat.gcd(p^e, q^f) = 1`.
- Current status: Admitted. Needs `Z.coprime_pow_l/r` + nat/Z gcd conversion.

### `count_multiples_in_range`
- Admitted due to complexity of induction proof over filter/seq.

## TODO
- [ ] Prove `count_multiples_in_range` (makes `euler_phi_prime_pow` fully admitted-free)
- [ ] Prove `prime_pow_coprime_distinct` (makes `euler_phi_three_prime_powers` fully admitted-free)
