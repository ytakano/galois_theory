# Proof Progress: znz_units_pow2_structure

## Status Overview
- Overall: In Progress
- Complete Lemmas: 14/18 (plus 2 helper lemmas proved)
- Unproven (`Admitted`): `inj_hom_surj_of_eq_order`, `one_plus_pow2_r_pow_s`, `congr_pow_mod`, `znz_units_pow2_structure`
- Failed/Abandoned Items: none

## Completed Lemmas

### Phase 0: Arithmetic Basics
All Phase 0 lemmas proved (in integer.v): `two_pow_ge2_gt_one`, `two_pow_nm2_pos`, `euler_phi_two_pow`, `znz_units_pow2_order`, `znz_to_nat_lt`, `znz_group_order_n`.

### Phase 1: Unit element tests
All proved in integer.v:
- `five_gcd_pow2`
- `neg_one_gcd_pow2`
- `five_pow_mod_four` (uses `compute. reflexivity.` not `simpl. lia.` in Z_scope)

### Phase 2: Key congruences
- `five_pow_two_k_congr` — proved; needs `rewrite Hy4, Hy3, HAs. ring.` (Hy3 required!)
- `five_pow_2k_s_congr` — proved
- `one_plus_pow2_r_pow_s` — Admitted (not needed for main chain)
- `congr_pow_mod` — Admitted (not needed for main chain)

### Phase 3: Order of 5
- `five_pow_pow2_nm2_one` — proved; key: use `rewrite H2n, H2n1 in Hq` then `nia` (not `lia`!)
- `nat_pow2_odd_decomp` — proved (strong induction via `lt_wf_ind`)
- `pow2_times2` (helper) — proved
- `odd_mul_pow2_not_zero_mod` — proved
`five_pow_not_one_before` - proved 

### Phase 4: Order of -1
- `neg_one_sq_one_pow2` — proved: `exists (Z.of_nat (Nat.pow 2 n) - 2). ring.`
- `neg_one_ne_one_pow2` — proved: `Z.mod_small by lia` (NOT `Z.pred_mod` — doesn't exist in Rocq 9.1)

## Proof Attempts & Diagnostics

### `five_pow_not_one_before`
- Status: Proved
- Key steps:
  1. Decompose `s = 2^k * t` with `t` odd using `nat_pow2_odd_decomp`
  2. Show `k < n-2` from `s < 2^(n-2)` and `2^k ≤ s`
  3. Use `five_pow_2k_s_congr k t` to get `2^(k+3) | 5^s - 1 - t*2^(k+2)`
  4. Since `2^n | 5^s - 1` and `2^(k+3) | 2^n`, get `2^(k+3) | 5^s - 1`
  5. Subtract: `2^(k+3) | t * 2^(k+2)`, hence `2 | t`
  6. But `t` is odd. Contradiction.
- Key tactic: `nia` for cancellation `(Z.of_nat t * 2^k+2) = r*(2*2^k+2) → Z.of_nat t = r*2`

## TODO
- [ ] `inj_hom_surj_of_eq_order` — inject hom + equal orders → surjective
- [ ] `znz_units_pow2_structure` — main theorem (Phase 5)
- [ ] `one_plus_pow2_r_pow_s`, `congr_pow_mod` — may remain Admitted if not needed

## Key Technical Notes
- `linarith` does NOT exist in Rocq 9.1; use `lia` instead
- `nlinarith` does NOT exist in Rocq 9.1; use `nia` for nonlinear
- `Z.pred_mod` does NOT exist in Rocq 9.1; use `Z.mod_small by lia` instead
- `simpl. lia.` on `5 mod 4 = 1` fails; use `compute. reflexivity.`
- `ring_simplify` fails on `Z.of_nat` terms; avoid it
- `Z.pow_add_r` global rewrite is dangerous; use explicit args form
