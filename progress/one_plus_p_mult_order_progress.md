# Proof Progress: one_plus_p_mult_order

## Status Overview
- Overall: Complete
- Complete Lemmas: 1/1
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `one_plus_p_mult_order`

```coq
Lemma one_plus_p_mult_order : forall (p n : nat)
    (Hp2 : (2 <= p)%nat)
    (Hprime : prime (Z.of_nat p))
    (Hodd : p <> 2%nat)
    (Hn : (1 <= n)%nat)
    (Hpn : (1 < p^n)%nat)
    (Hm : GroupOrder (znz_units_group (p^n) Hpn) (p^(n-1) * (p-1)))
    (elem : carrier (znz_units_group (p^n) Hpn))
    (Helem : proj1_sig elem = (1 + Z.of_nat p) mod Z.of_nat (p^n)),
    mult_order (znz_units_group (p^n) Hpn) (p^(n-1) * (p-1)) Hm elem = (p^(n-1))%nat.
```

Proof compiled 2026-04-08.

## TODO
(none)
