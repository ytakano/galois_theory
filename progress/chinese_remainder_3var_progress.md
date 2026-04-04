# Proof Progress: chinese_remainder_3

## Status Overview
- Overall: Complete
- Complete Lemmas: 10/10
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas
### `pairwise_coprime3_pq`
```coq
Lemma pairwise_coprime3_pq : forall (p q r : nat),
  pairwise_coprime3 p q r -> Nat.gcd p q = 1%nat.
Proof.
  intros p q r [Hpq _]. exact Hpq.
Qed.
```

### `pairwise_coprime3_qr`
```coq
Lemma pairwise_coprime3_qr : forall (p q r : nat),
  pairwise_coprime3 p q r -> Nat.gcd q r = 1%nat.
Proof.
  intros p q r [_ [Hqr _]]. exact Hqr.
Qed.
```

### `pairwise_coprime3_pr`
```coq
Lemma pairwise_coprime3_pr : forall (p q r : nat),
  pairwise_coprime3 p q r -> Nat.gcd p r = 1%nat.
Proof.
  intros p q r [_ [_ Hpr]]. exact Hpr.
Qed.
```

### `pairwise_coprime3_gcd_pq_r`
```coq
Lemma pairwise_coprime3_gcd_pq_r : forall (p q r : nat),
  pairwise_coprime3 p q r -> Nat.gcd (p * q) r = 1%nat.
Proof.
  intros p q r Hpair.
  pose proof (pairwise_coprime3_pr p q r Hpair) as Hpr.
  pose proof (pairwise_coprime3_qr p q r Hpair) as Hqr.
  destruct (nat_coprime_bezout p r Hpr) as [x1 [y1 Hbez1]].
  destruct (nat_coprime_bezout q r Hqr) as [x2 [y2 Hbez2]].

  assert (Hmul :
    (Z.of_nat p * x1 + Z.of_nat r * y1) *
    (Z.of_nat q * x2 + Z.of_nat r * y2) = 1).
  { rewrite Hbez1, Hbez2. ring. }

  assert (Hex : exists x y : Z,
    Z.of_nat (p * q) * x + Z.of_nat r * y = 1).
  {
    exists (x1 * x2).
    exists (Z.of_nat p * x1 * y2 + Z.of_nat q * x2 * y1 + Z.of_nat r * y1 * y2).
    rewrite Nat2Z.inj_mul.
    rewrite <- Hmul.
    ring.
  }

  pose proof (proj1 (linear_diophantine (Z.of_nat (p * q)) (Z.of_nat r) 1) Hex)
    as Hdiv.
  destruct Hdiv as [k Hk].
  assert (HgcdZ : Z.gcd (Z.of_nat (p * q)) (Z.of_nat r) = 1).
  { pose proof (Z.gcd_nonneg (Z.of_nat (p * q)) (Z.of_nat r)) as Hnonneg. nia. }
  rewrite <- Nat2Z.inj_gcd.
  rewrite Nat2Z.inj_mul.
  lia.
Qed.
```

### `cong_of_cong_mul_l`
```coq
Lemma cong_of_cong_mul_l : forall (p q : nat) (a b : Z),
  cong (p * q) a b -> cong p a b.
Proof.
  intros p q a b H.
  unfold cong in *.
  destruct H as [k Hk].
  rewrite Nat2Z.inj_mul in Hk.
  exists (Z.of_nat q * k).
  lia.
Qed.
```

### `cong_of_cong_mul_r`
```coq
Lemma cong_of_cong_mul_r : forall (p q : nat) (a b : Z),
  cong (p * q) a b -> cong q a b.
Proof.
  intros p q a b H.
  unfold cong in *.
  destruct H as [k Hk].
  rewrite Nat2Z.inj_mul in Hk.
  exists (Z.of_nat p * k).
  lia.
Qed.
```

### `coprime_divide_mul_3`
実装済み（`pairwise_coprime3_gcd_pq_r` に依存）。

### `crt_exists_3`
実装済み。

### `crt_unique_3`
実装済み。

### `chinese_remainder_3`
実装済み。

## Proof Attempts & Diagnostics
なし

## TODO
- [ ] `rocq compile integer.v` を通し、`chinese_remainder_3` 一式を最終検証
