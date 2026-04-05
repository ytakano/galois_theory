# Proof Progress: euler_phi (Euler's Totient Function)

## Status Overview
- Overall: **Complete** (all lemmas proven, no Admitted)
- Complete Lemmas: 12/12 (T1-T12, including all sub-lemmas)
- Unproven (Admitted): none
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

### T9 sub-lemmas (new): `mod_add_mul_small`, `filter_false_forall`, `filter_window_single_multiple`

**`mod_add_mul_small`**: `0 < p → r < p → (p * m + r) mod p = r`
- Proof: `Nat.mul_comm + Nat.add_comm + Nat.Div0.mod_add + Nat.mod_small`

**`filter_false_forall`**: `Forall (fun x => f x = false) l → filter f l = []`
- Proof: induction on Forall with `cbn [List.filter]`

**`filter_window_single_multiple`**: `0 < p → filter (k mod p =? 0) (seq (p*m) p) = [p*m]`
- Proof: `destruct p as [| p']`; use `cbn [List.seq]; cbn [List.filter]`; head passes (mod_mul), tail filtered out via `filter_false_forall` + `mod_add_mul_small`

### T9: `count_multiples_in_range`
Proven. `0 < p → length (filter (k mod p =? 0) (seq 0 (p*m))) = m`
- Proof: induction on m; split `seq 0 (p*S m') = seq 0 (p*m') ++ seq (p*m') p` via `seq_app`; use `filter_window_single_multiple` for the window; IH for the prefix.

### T10: `euler_phi_prime_pow`
Proven. `euler_phi(p^e) = p^(e-1) * (p-1)` for prime p and e ≥ 1 (now fully admitted-free).

### T11: `prime_pow_coprime_distinct`
Proven. `prime p → prime q → p ≠ q → Nat.gcd(p^e, q^f) = 1`
- Proof (3 steps):
  1. `Z.gcd(p, q) = 1` via `prime_divisors` + `prime_ge_2` + `Zis_gcd_gcd` + `prime_rel_prime`
  2. `Z.gcd(p^e, q^f) = 1` via `Nat2Z.inj_pow` + `Z.coprime_pow_l` + `Z.coprime_pow_r`
  3. `Nat.gcd(p^e, q^f) = 1` via `Z.gcd_greatest` + `Z.divide_1_r` + `Nat2Z.inj`

### T11b: `nat_gcd_mul_coprime`
Proven. `Nat.gcd a c = 1 → Nat.gcd b c = 1 → Nat.gcd(a*b, c) = 1` via Gauss's lemma.

### T12: `euler_phi_three_prime_powers` — MAIN THEOREM
Proven (now fully admitted-free).
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

(all issues resolved — see history for past attempts)

## TODO
(all done)

- [ ] Prove `prime_pow_coprime_distinct` (makes `euler_phi_three_prime_powers` fully admitted-free)
