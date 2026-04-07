# Proof Plan: one_plus_p_mult_order

## Goal
```coq
Lemma one_plus_p_mult_order : forall (p n : nat)
    (Hp2 : (2 <= p)%nat)
    (Hprime : prime (Z.of_nat p))
    (Hodd : p <> 2)
    (Hn : (1 <= n)%nat)
    (Hpn : (1 < p^n)%nat)
    (Hm : GroupOrder (znz_units_group (p^n) Hpn) (p^(n-1) * (p-1)))
    (elem : carrier (znz_units_group (p^n) Hpn))
    (Helem : proj1_sig elem = (1 + Z.of_nat p) mod Z.of_nat (p^n)),
    mult_order (znz_units_group (p^n) Hpn) (p^(n-1) * (p-1)) Hm elem = p^(n-1).
```

## Proof Strategy

1. Upper bound: `one_plus_p_pow_pk_dvd` → `gpow_nat G elem (p^(n-1)) = e G` → `d | p^(n-1)`
2. `nat_prime_pow_divisors` → `d = p^k`, `k ≤ n-1`
3. Lower bound (n ≥ 2): `one_plus_p_pow_pk_not_dvd` → `gpow_nat G elem (p^(n-2)) ≠ e G` → `¬(d | p^(n-2))`
4. If `k ≤ n-2` then `p^k | p^(n-2)` → contradiction → `k = n-1`

## Proof Order
1. `one_plus_p_mult_order` (main)
