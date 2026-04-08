# Proof Progress: znz_units_is_cyclic_product

## Status Overview
- Overall: **Complete** (2026-04-08)
- Complete Lemmas: 11/11
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `IsCyclicProduct` (Definition)
```coq
Inductive IsCyclicProduct : Group -> Prop :=
  | ICP_cyclic  : forall C : CyclicGroup, IsCyclicProduct C
  | ICP_product : forall G H : Group,
      IsCyclicProduct G -> IsCyclicProduct H ->
      IsCyclicProduct (G ×ₒ H)
  | ICP_iso     : forall G H : Group,
      G ≅ H -> IsCyclicProduct H -> IsCyclicProduct G.
```

### `icp_znz_group`
```coq
Lemma icp_znz_group : forall (n : nat) (Hn : (0 < n)%nat),
  IsCyclicProduct (znz_group n Hn).
```
`exact (ICP_cyclic (znz_cyclic_group n Hn))`.

### `znz_units_2_order`
```coq
Lemma znz_units_2_order : forall (H2 : (1 < 2)%nat),
  GroupOrder (znz_units_group 2 H2) 1.
```
`compute; reflexivity` で `euler_phi 2 = 1` を示し `euler_phi_group_order` を適用。

### `group_order_1_is_cyclic`
```coq
Lemma group_order_1_is_cyclic : forall (G : Group),
  GroupOrder G 1 -> IsCyclicProduct G.
```
`Fin.caseS'` + `Fin.case0` で全元が `e G` に等しいことを示し、CyclicGroup を構成。

### `znz_units_pow2_is_cyclic_product`
```coq
Lemma znz_units_pow2_is_cyclic_product :
  forall (k : nat) (Hk : (1 <= k)%nat) (H2k : (1 < 2^k)%nat),
    IsCyclicProduct (znz_units_group (2^k) H2k).
```
k=1: `group_order_1_is_cyclic + znz_units_2_order`. k≥2: `znz_units_pow2_structure + ICP_iso + ICP_product`.

### `znz_units_odd_prime_pow_is_cyclic_product`
```coq
Lemma znz_units_odd_prime_pow_is_cyclic_product :
  forall (p k : nat) (Hp : (1 < p)%nat)
         (Hprime : prime (Z.of_nat p)) (Hodd : p <> 2%nat)
         (Hk : (1 <= k)%nat) (Hpk : (1 < p^k)%nat),
    IsCyclicProduct (znz_units_group (p^k) Hpk).
```
`znz_units_odd_prime_pow_cyclic + ICP_iso + icp_znz_group`.

### `znz_units_prime_pow_is_cyclic_product`
```coq
Lemma znz_units_prime_pow_is_cyclic_product :
  forall (p k : nat) (Hprime : prime (Z.of_nat p))
         (Hk : (1 <= k)%nat) (Hpk : (1 < p^k)%nat),
    IsCyclicProduct (znz_units_group (p^k) Hpk).
```
p=2 と奇素数で `Nat.eq_dec p 2` による場合分け。

### `nat_prime_divisor_exists`
```coq
Lemma nat_prime_divisor_exists :
  forall n : nat, (1 < n)%nat ->
  exists p : nat, prime (Z.of_nat p) /\ Nat.divide p n.
```
強帰納法 + `prime_dec` + `not_prime_divide` + `Z_divide_nat`.

### `prime_divides_exists_prime_power_split`
```coq
Lemma prime_divides_exists_prime_power_split :
  forall (p n : nat),
    prime (Z.of_nat p) -> (1 <= n)%nat -> (Z.of_nat p | Z.of_nat n) ->
    exists k m : nat,
      (1 <= k)%nat /\ (n = m * p^k)%nat /\ Nat.gcd m (p^k) = 1%nat.
```
強帰納法 + `prime_pow_coprime_iff` + `Z_gcd_of_nat` で p進分解を抽出。

### `znz_units_is_cyclic_product` (主定理)
```coq
Theorem znz_units_is_cyclic_product :
  forall (n : nat) (Hn : (1 < n)%nat),
    IsCyclicProduct (znz_units_group n Hn).
```
強帰納法 + `nat_prime_divisor_exists` + `prime_divides_exists_prime_power_split` + 場合分け。

## Proof Attempts & Diagnostics

### 技術的注意事項

- `Nat.mod_eq_0_iff_dvd.2`: `Nat.mod_eq_0_iff_dvd` が `(p | n) ↔ n mod p = 0` の形で使える。
- `Fin.caseS'` + `Fin.case0`: `Fin.t 1` の唯一の元が `Fin.F1` であることの証明に使用。
- `Z_gcd_of_nat` + `prime_pow_coprime_iff`: Z.gcd と Nat.gcd の橋渡し。
- `nia` で非線形不等式 `m < m * p^k` を処理。
- `by lia` 記法: Rocq 9.1 では `(by lia : (1 <= S k'))%nat` の形で使える。

## TODO
- (すべて完了)

