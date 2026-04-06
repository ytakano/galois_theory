# Proof Progress: primitive_root_exists

## Status Overview
- Overall: In Progress
- Complete Lemmas: 16/24 (Phase 2 complete)
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### Phase 1: Fermat's Little Theorem

### `op_cancel_r`
両辺右から逆元を掛けて `rewrite <- assoc, !inv_right, !id_right` で x = y を導く。

### `group_elements_list`
GroupOrder の全単射の逆像を epsilon で構成。`map g (fin_all n)` が NoDup・長さ n・全射。
NoDup は `NoDup_map_NoDup_ForallPairs` + g の単射性（f ∘ g = id）から。

### `znz_units_op_comm`
`apply sig_eq; simpl; rewrite Z.mul_comm; reflexivity`

### `fold_right_mul_left_abelian`
L についての帰納法。再帰ステップは assoc × 2 + G_abelian + assoc × 2 の rewrite 列。

### `znz_units_mul_left_permutation`
`NoDup_Permutation` を使用。NoDup は `op_cancel_l` の単射性から。
双方向 In は逆元の存在（inv G a）から。

### `fold_right_permutation_abelian`
Permutation の帰納法。perm_swap ケースは `assoc + G_abelian + ← assoc`。

### `fermat_little_theorem`
全元リスト L、置換 → fold 不変性 → fold = a^(p-1) * fold → op_cancel_r で a^(p-1) = e。

### `mult_order_p_divides_p_minus_1`
`proj1 (mult_order_p_divides ...) + fermat_little_theorem`

### Phase 2: Polynomial root bound → order_d_elements_are_powers

### `znz_units_to_field`
`znz_units_group p Hp` から `znz_p_field p Hprime` への埋め込み写像。
carrier を `exist _ (proj1_sig x) (proj1 (proj2_sig x))` で定義。

### `znz_units_to_field_mul`
`apply sig_eq; simpl; reflexivity` で乗法準同型を示す。

### `znz_units_to_field_one`
`apply sig_eq; simpl; symmetry; apply Z.mod_small` で単位元保存を示す。
`prime_ge_2 in Hprime; lia` で 1 mod p = 1 を確認。

### `znz_units_to_field_pow`
帰納法 + `change (...)` で inductive step のゴールを明示的に書いて
`rewrite IH; apply znz_units_to_field_mul`。

### `znz_units_to_field_inj`
`apply sig_eq; change (...); f_equal (fun e : ring_carrier F => proj1_sig e)`。
型アノテーションで `f_equal` の型推論を助ける。

### `xd_poly`, `xd_minus_1_poly`
`xd_poly F n = repeat (ring_zero F) n ++ [ring_one F]` を induction で確認し
`List.last_last` で `xd_poly_last` を証明。
`last_nonempty_cons` を追加: `l ≠ nil → last (a :: l) d = last l d`。
`xd_minus_1_poly_nonzero_leading` は `last_nonempty_cons + xd_poly_last + field_one_ne_zero`。

### `gpow_is_field_root`
`rewrite xd_minus_1_poly_eval, znz_units_to_field_pow, Hxd, znz_units_to_field_one`。
`apply ring_add_neg_l`。

### `NoDup_field_powers`
`NoDup_map_NoDup_ForallPairs + znz_units_to_field_inj + mult_order_p_powers_distinct`。

### `order_d_elements_are_powers`
背理法: x が a の冪乗でないと仮定し、roots = {a^0,...,a^(d-1)} ∪ {x} の d+1 個が
x^d-1 = 0 の根。`fp_poly_roots_bound` より d+1 < d+1、矛盾。
Key fixes:
- `znz_units_to_field_inj p Hp Hprime` を明示的に適用 (set G でブロックされるため)
- `eq_sym Hy2` で等号方向を修正
- `rewrite <- gpow_nat_mul; apply (proj2 (mult_order_p_divides ... (k * d))); unfold Nat.divide; exists k; lia`
- `exact Hr` → `contradiction` (Hr : False のケース)

## Proof Attempts & Diagnostics
(none)

## TODO
- [ ] `order_of_power_gcd` (Phase 3)
- [ ] `psi_le_phi` (Phase 4)
- [ ] `divisors_list` + `sum_phi_over_divisors` (Phase 5)
- [ ] `sum_psi_over_divisors` (Phase 6)
- [ ] `psi_eq_phi_all` (Phase 6)
- [ ] `euler_phi_pos` (Phase 6)
- [ ] `primitive_root_exists` (main theorem)
