# Proof Plan: znz_units_group_cyclic_iso

## Goal

素数 p に対して、(Z/pZ)* は位数 p-1 の巡回群 Z/(p-1)Z に同型である:

```coq
Theorem znz_units_group_cyclic_iso :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p)),
    exists Hp1 : (0 < p - 1)%nat,
      znz_units_group p Hp ≅ znz_group (p - 1) Hp1.
```

## Proof Strategy

3フェーズに分解する:

**Phase 1**: `znz_units_cyclic_group` — (Z/pZ)* に CyclicGroup 構造を与える  
**Phase 2**: `cyclic_group_isomorphic_znz` — 位数 n の CyclicGroup は Z/nZ に同型（抽象定理）  
**Phase 3**: 主定理 = Phase 1 + Phase 2 の結合

## Proposed Lemmas

### Phase 1

- [x] `primitive_root_generates_all`: 位数 p-1 の元 g が (Z/pZ)* 全体を生成する
  - fermat_little_theorem + order_d_elements_are_powers → ∀ a, ∃ k : Z, gpow G g k = a

- [x] `znz_units_cyclic_group` (Definition): primitive_root_exists を使って CyclicGroup レコード構築

### Phase 2

- [x] `generator_mult_order_eq_group_order`: 位数 n の CyclicGroup の生成元 mult_order = n
  - mult_order_spec: d ≤ n (generator_order より g^n = e)
  - cyclic_group_order_le_period: n ≤ d (g^d = e より)
  - 結論: d = n

- [x] `cyclic_powers_injective`: r1 < n, r2 < n, g^r1 = g^r2 → r1 = r2
  - generator_mult_order_eq_group_order + mult_order_powers_distinct

- [x] `gpow_nat_mod`: g^n = e → gpow_nat G g (k mod n) = gpow_nat G g k
  - Nat.div_mod + gpow_nat_period_cancel

- [x] `cyc_index` (Definition) + `cyc_index_spec` (Lemma):
  - cyc_index C n Hord x := epsilon 0 (fun r => r < n ∧ gpow_nat C g r = x)
  - cyc_index x < n かつ gpow_nat C g (cyc_index x) = x
  - 存在: generator_order + gpow_reduce_mod + gpow_of_nat
  - 一意性: cyclic_powers_injective

- [x] `cyc_index_unique`: r < n ∧ gpow_nat g r = x → r = cyc_index x
  - cyclic_powers_injective + cyc_index_spec

- [x] `cyc_index_homo`: cyc_index (x * y) = (cyc_index x + cyc_index y) mod n
  - gpow_nat_add + gpow_nat_mod + cyc_index_unique

- [x] `cyclic_group_isomorphic_znz`:
  - 同型写像 f(x) = [Z.of_nat (cyc_index x)] : C → znz_group n Hn
  - 準同型: cyc_index_homo + Nat2Z.inj_mod + Nat2Z.inj_add
  - 単射: sig_eq → Nat2Z.inj → cyc_index_spec
  - 全射: gpow_nat g (Z.to_nat k) ↦ k via cyc_index_unique + Z2Nat.id

### Phase 3

- [x] `znz_units_group_cyclic_iso` (主定理):
  - znz_units_cyclic_group + prime_units_group_order + cyclic_group_isomorphic_znz

## Proof Order

1. `primitive_root_generates_all`
2. `znz_units_cyclic_group`
3. `generator_mult_order_eq_group_order`
4. `cyclic_powers_injective`
5. `gpow_nat_mod`
6. `cyc_index` + `cyc_index_spec`
7. `cyc_index_unique`
8. `cyc_index_homo`
9. `cyclic_group_isomorphic_znz`
10. `znz_units_group_cyclic_iso` (main goal)
