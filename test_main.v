Require Import integer.
From Stdlib Require Import ZArith Lia Arith.
Open Scope Z_scope.

Lemma Zpow_mod_period_Z : forall (b N M a : Z),
    1 < N -> 0 < M -> 0 <= a ->
    b ^ M mod N = 1 ->
    b ^ a mod N = b ^ (a mod M) mod N.
Proof.
  intros b N M a HN HM Ha Hperiod.
  set (q := a / M). set (r := a mod M).
  assert (Hq : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  assert (HM0 : 0 <= M) by lia.
  assert (Hr : 0 <= r < M) by (unfold r; apply Z.mod_pos_bound; lia).
  assert (Hdiv : a = M * q + r) by (unfold q, r; pose proof (Z.div_mod a M ltac:(lia)) as H; lia).
  rewrite Hdiv. rewrite Z.pow_add_r by lia. rewrite (Z.pow_mul_r b M q HM0 Hq).
  assert (Hbmq : (b ^ M) ^ q mod N = 1).
  { rewrite <- Z.mod_pow_l. rewrite Hperiod. rewrite (Z.pow_1_l q Hq). apply Z.mod_1_l. lia. }
  rewrite Z.mul_mod by lia. rewrite Hbmq. rewrite Z.mul_1_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma phi_hom_val : forall (N M a1 a2 b1 b2 : Z),
    1 < N -> 0 < M ->
    0 <= a1 < M -> 0 <= a2 < M ->
    0 <= b1 < 2 -> 0 <= b2 < 2 ->
    (5:Z)^M mod N = 1 ->
    (N - 1)^2 mod N = 1 ->
    (5:Z)^((a1 + a2) mod M) * (N-1)^((b1+b2) mod 2) mod N =
    (5:Z)^a1 * (N-1)^b1 * ((5:Z)^a2 * (N-1)^b2) mod N.
Proof.
  intros N M a1 a2 b1 b2 HN HM Ha1 Ha2 Hb1 Hb2 H5 HN1.
  assert (HRHS : (5:Z)^a1 * (N-1)^b1 * ((5:Z)^a2 * (N-1)^b2) =
                 (5:Z)^(a1+a2) * (N-1)^(b1+b2)).
  { rewrite Z.pow_add_r by lia. rewrite Z.pow_add_r by lia. ring. }
  rewrite HRHS.
  assert (H5eq : (5:Z)^((a1+a2) mod M) mod N = (5:Z)^(a1+a2) mod N).
  { symmetry. apply Zpow_mod_period_Z; [lia | lia | lia | exact H5]. }
  assert (HN1eq : (N-1)^((b1+b2) mod 2) mod N = (N-1)^(b1+b2) mod N).
  { symmetry. apply (Zpow_mod_period_Z (N-1) N 2); [lia | lia | lia | exact HN1]. }
  rewrite Z.mul_mod by lia.
  rewrite H5eq. rewrite HN1eq.
  rewrite <- Z.mul_mod by lia.
  reflexivity.
Qed.

Lemma phi_b_one_contradiction : forall (N a : Z),
    (4 | N) -> 1 < N ->
    (5:Z)^a mod 4 = 1 ->
    (5:Z)^a * (N-1) mod N = 1 ->
    False.
Proof.
  intros N a H4N HN H5mod Hphi.
  assert (HN_ge4 : 4 <= N) by (destruct H4N as [k Hk]; lia).
  assert (HNm1 : (N - 1) mod 4 = 3).
  { destruct H4N as [k Hk].
    assert (H : N - 1 = 3 + (k - 1) * 4) by lia.
    rewrite H. rewrite Z.mod_add by lia. compute. reflexivity. }
  assert (H4dvd : (4 | (5:Z)^a * (N-1) - 1)).
  { apply (Z.divide_trans 4 N _); [exact H4N|].
    apply Z.mod_divide; [lia|].
    rewrite Zminus_mod. rewrite Hphi.
    rewrite Z.mod_1_l by lia. rewrite Z.sub_diag. apply Z.mod_0_l. lia. }
  assert (Hmod4 : (5:Z)^a * (N-1) mod 4 = 1).
  { destruct H4dvd as [q Hq]. assert (Hh : (5:Z)^a * (N-1) = 1 + q * 4) by lia.
    rewrite Hh. rewrite Z.mod_add by lia. compute. reflexivity. }
  rewrite Z.mul_mod in Hmod4 by lia.
  rewrite H5mod, HNm1 in Hmod4.
  compute in Hmod4. discriminate.
Qed.



Lemma five_pow_1_implies_zero : forall n (Hn : (2 <= n)%nat) (Hn2 : (0 < Nat.pow 2 (n-2))%nat)
    (a : Z) (Ha : 0 <= a < Z.of_nat (Nat.pow 2 (n-2))),
    (Z.of_nat (Nat.pow 2 n) | (5:Z)^a - 1) -> a = 0.
Proof.
  intros n Hn Hn2 a Ha Hdvd.
  destruct (Z.eq_dec a 0) as [Ha0|Ha0]. exact Ha0.
  assert (Hapos : 0 < a) by lia.
  destruct (Nat.eq_dec n 2) as [Hn2'|Hn3'].
  - subst n. simpl in Ha. lia.
  - assert (H3 : (3 <= n)%nat) by lia.
    assert (Hs_pos : (0 < Z.to_nat a)%nat).
    { apply (Z2Nat.inj_lt 0 a ltac:(lia) ltac:(lia)). lia. }
    assert (Hs_lt : (Z.to_nat a < Nat.pow 2 (n-2))%nat).
    { assert (H : (Z.to_nat a < Z.to_nat (Z.of_nat (Nat.pow 2 (n-2))))%nat)
        by (apply (Z2Nat.inj_lt a (Z.of_nat (Nat.pow 2 (n-2))) ltac:(lia) ltac:(lia)); lia).
      rewrite Nat2Z.id in H. exact H. }
    assert (Hpow : Z.of_nat (Z.to_nat a) = a) by (apply Z2Nat.id; lia).
    assert (HNdvd' : (Z.of_nat (Nat.pow 2 n) | (5:Z)^(Z.of_nat (Z.to_nat a)) - 1)).
    { rewrite Hpow. exact Hdvd. }
    exact (False_ind _ (five_pow_not_one_before n (Z.to_nat a) H3 Hs_pos Hs_lt HNdvd')).
Qed.

Lemma five_pow_eq_implies_equal : forall n (Hn : (2 <= n)%nat) (H2n : (1 < Nat.pow 2 n)%nat) (Hn2 : (0 < Nat.pow 2 (n-2))%nat)
    (a1 a2 : Z)
    (Ha1 : 0 <= a1 < Z.of_nat (Nat.pow 2 (n-2)))
    (Ha2 : 0 <= a2 < Z.of_nat (Nat.pow 2 (n-2))),
    (Z.of_nat (Nat.pow 2 n) | (5:Z)^a1 - (5:Z)^a2) -> a1 = a2.
Proof.
  intros n Hn H2n Hn2 a1 a2 Ha1 Ha2 Hdvd.
  set (N := Z.of_nat (Nat.pow 2 n)).
  set (M := Z.of_nat (Nat.pow 2 (n-2))).
  assert (HN_gt1 : 1 < N).
  { unfold N. assert ((4 <= Nat.pow 2 n)%nat)
      by (change (4%nat) with (Nat.pow 2 2); apply Nat.pow_le_mono_r; lia). lia. }
  assert (Hgcd5N : Z.gcd 5 N = 1) by (unfold N; apply five_gcd_pow2; lia).
  destruct (Z_lt_le_dec a1 a2) as [Hlt|Hle].
  - assert (Hfact : (5:Z)^a1 - (5:Z)^a2 = -((5:Z)^a1 * ((5:Z)^(a2-a1) - 1))).
    { replace ((5:Z)^a2) with ((5:Z)^(a1 + (a2-a1))) by (f_equal; lia).
      rewrite Z.pow_add_r by lia. ring. }
    assert (HNdvd_prod : (N | (5:Z)^a1 * ((5:Z)^(a2-a1) - 1))).
    { apply (Z.divide_opp_r N ((5:Z)^a1 * ((5:Z)^(a2-a1) - 1))).
      rewrite <- Hfact. exact Hdvd. }
    assert (Hgcd5a1N : Z.gcd ((5:Z)^a1) N = 1).
    { exact (Z.coprime_pow_l 5 N a1 (proj1 Ha1) Hgcd5N). }
    assert (HNdvd : (N | (5:Z)^(a2-a1) - 1)).
    { exact (Z.gauss N ((5:Z)^a1) ((5:Z)^(a2-a1) - 1) HNdvd_prod
                     (eq_trans (Z.gcd_comm N ((5:Z)^a1)) Hgcd5a1N)). }
    assert (Ha_diff : 0 <= a2 - a1 < M) by (unfold M; lia).
    pose proof (five_pow_1_implies_zero n Hn Hn2 (a2-a1) Ha_diff HNdvd). lia.
  - assert (Hfact : (5:Z)^a1 - (5:Z)^a2 = (5:Z)^a2 * ((5:Z)^(a1-a2) - 1)).
    { replace ((5:Z)^a1) with ((5:Z)^(a2 + (a1-a2))) by (f_equal; lia).
      rewrite Z.pow_add_r by lia. ring. }
    assert (HNdvd_prod : (N | (5:Z)^a2 * ((5:Z)^(a1-a2) - 1))).
    { rewrite <- Hfact. exact Hdvd. }
    assert (Hgcd5a2N : Z.gcd ((5:Z)^a2) N = 1).
    { exact (Z.coprime_pow_l 5 N a2 (proj1 Ha2) Hgcd5N). }
    assert (HNdvd : (N | (5:Z)^(a1-a2) - 1)).
    { exact (Z.gauss N ((5:Z)^a2) ((5:Z)^(a1-a2) - 1) HNdvd_prod
                     (eq_trans (Z.gcd_comm N ((5:Z)^a2)) Hgcd5a2N)). }
    assert (Ha_diff : 0 <= a1 - a2 < M) by (unfold M; lia).
    pose proof (five_pow_1_implies_zero n Hn Hn2 (a1-a2) Ha_diff HNdvd). lia.
Qed.

(* Now prove the full injectivity *)
Lemma phi_inj : forall n (Hn : (2 <= n)%nat) (H2n : (1 < Nat.pow 2 n)%nat) (Hn2 : (0 < Nat.pow 2 (n-2))%nat),
  let N := Z.of_nat (Nat.pow 2 n) in
  let M := Z.of_nat (Nat.pow 2 (n-2)) in
  forall (a1 a2 : {x : Z | 0 <= x < M}) (b1 b2 : {x : Z | 0 <= x < 2}),
  (5:Z)^(proj1_sig a1) * (N-1)^(proj1_sig b1) mod N =
  (5:Z)^(proj1_sig a2) * (N-1)^(proj1_sig b2) mod N ->
  a1 = a2 /\ b1 = b2.
Proof.
  intros n Hn H2n Hn2 N M a1 a2 b1 b2 Hval_eq.
  set (av1 := proj1_sig a1). set (av2 := proj1_sig a2).
  set (bv1 := proj1_sig b1). set (bv2 := proj1_sig b2).
  assert (Ha1 := proj2_sig a1 : 0 <= av1 < M).
  assert (Ha2 := proj2_sig a2 : 0 <= av2 < M).
  assert (Hb1 := proj2_sig b1 : 0 <= bv1 < 2).
  assert (Hb2 := proj2_sig b2 : 0 <= bv2 < 2).
  assert (HN_gt1 : 1 < N).
  { unfold N. assert ((4 <= Nat.pow 2 n)%nat)
      by (change (4%nat) with (Nat.pow 2 2); apply Nat.pow_le_mono_r; lia). lia. }
  assert (H4N : (4 | N)).
  { unfold N. exists (Z.of_nat (Nat.pow 2 (n-2))).
    assert (H4 : (4 * Nat.pow 2 (n-2) = Nat.pow 2 n)%nat).
    { change (4%nat) with (Nat.pow 2 2). rewrite <- Nat.pow_add_r. f_equal. lia. }
    zify. lia. }
  assert (HNm1_4 : (N - 1) mod 4 = 3).
  { destruct H4N as [k Hk].
    assert (H : N - 1 = 3 + (k - 1) * 4) by lia.
    rewrite H. rewrite Z.mod_add by lia. compute. reflexivity. }
  (* 5^av mod 4 = 1 for any av >= 0 *)
  assert (H5av1_4 : (5:Z)^av1 mod 4 = 1).
  { pose proof (five_pow_mod_four (Z.to_nat av1)) as H.
    rewrite Z2Nat.id in H by (exact (proj1 Ha1)). exact H. }
  assert (H5av2_4 : (5:Z)^av2 mod 4 = 1).
  { pose proof (five_pow_mod_four (Z.to_nat av2)) as H.
    rewrite Z2Nat.id in H by (exact (proj1 Ha2)). exact H. }
  (* Get mod 4 equality from val_eq *)
  assert (Hmod4_eq : (5:Z)^av1 * (N-1)^bv1 mod 4 = (5:Z)^av2 * (N-1)^bv2 mod 4).
  { (* From N | (5^av1*(N-1)^bv1 - 5^av2*(N-1)^bv2), 4 | N => 4 | diff *)
    assert (HN_diff : (N | (5:Z)^av1 * (N-1)^bv1 - (5:Z)^av2 * (N-1)^bv2)).
    { apply Z.mod_divide; [lia|].
      rewrite Zminus_mod. unfold av1, bv1, av2, bv2. rewrite Hval_eq.
      rewrite Z.sub_diag. apply Z.mod_0_l. lia. }
    assert (H4_diff : (4 | (5:Z)^av1 * (N-1)^bv1 - (5:Z)^av2 * (N-1)^bv2)).
    { exact (Z.divide_trans 4 N _ H4N HN_diff). }
    assert (H4_zero : ((5:Z)^av1 * (N-1)^bv1 - (5:Z)^av2 * (N-1)^bv2) mod 4 = 0).
    { apply Z.mod_divide; [lia | exact H4_diff]. }
    assert (HLmod : (5:Z)^av1 * (N-1)^bv1 mod 4 = ((5:Z)^av1 * (N-1)^bv1 - (5:Z)^av2 * (N-1)^bv2 + (5:Z)^av2 * (N-1)^bv2) mod 4).
    { f_equal. lia. }
    rewrite HLmod. rewrite Zplus_mod. rewrite H4_zero. simpl. rewrite Z.mod_mod by lia. reflexivity. }
  (* bv1 = bv2 *)
  assert (Hbv12 : bv1 = bv2).
  { (* Compute mod 4 for each bv value *)
    assert (Hlhs : (5:Z)^av1 * (N-1)^bv1 mod 4 = (N-1)^bv1 mod 4).
    { rewrite Z.mul_mod by lia. rewrite H5av1_4. rewrite Z.mul_1_l. apply Z.mod_mod. lia. }
    assert (Hrhs : (5:Z)^av2 * (N-1)^bv2 mod 4 = (N-1)^bv2 mod 4).
    { rewrite Z.mul_mod by lia. rewrite H5av2_4. rewrite Z.mul_1_l. apply Z.mod_mod. lia. }
    rewrite Hlhs, Hrhs in Hmod4_eq.
    (* bv in {0, 1}: (N-1)^0 mod 4 = 1, (N-1)^1 mod 4 = 3 *)
    destruct (Z.eq_dec bv1 0) as [Hbv10|Hbv11]; destruct (Z.eq_dec bv2 0) as [Hbv20|Hbv21].
    - lia.
    - exfalso. assert (Hbv2one : bv2 = 1) by lia.
      rewrite Hbv10, Hbv2one in Hmod4_eq.
      rewrite Z.pow_0_r, Z.pow_1_r, HNm1_4 in Hmod4_eq.
      compute in Hmod4_eq. discriminate.
    - exfalso. assert (Hbv1one : bv1 = 1) by lia.
      rewrite Hbv1one, Hbv20 in Hmod4_eq.
      rewrite Z.pow_1_r, Z.pow_0_r, HNm1_4 in Hmod4_eq.
      compute in Hmod4_eq. discriminate.
    - lia. }
  (* av1 = av2 *)
  assert (Hav12 : av1 = av2).
  { (* With bv1 = bv2, 5^av1 * (N-1)^bv1 mod N = 5^av2 * (N-1)^bv1 mod N *)
    assert (Hval5 : (5:Z)^av1 * (N-1)^bv1 mod N = (5:Z)^av2 * (N-1)^bv1 mod N).
    { assert (Hb12_val : proj1_sig b1 = proj1_sig b2) by (unfold bv1, bv2 in Hbv12; exact Hbv12).
      unfold av1, bv1, av2, bv2.
      rewrite <- Hb12_val in Hval_eq. exact Hval_eq. }
    (* N | 5^av1*(N-1)^bv1 - 5^av2*(N-1)^bv1 = (N-1)^bv1 * (5^av1 - 5^av2) *)
    assert (HN_diff2 : (N | (N-1)^bv1 * ((5:Z)^av1 - (5:Z)^av2))).
    { apply Z.mod_divide; [lia|].
      assert (Heq5 : (N-1)^bv1 * ((5:Z)^av1 - (5:Z)^av2) =
                     (5:Z)^av1 * (N-1)^bv1 - (5:Z)^av2 * (N-1)^bv1) by ring.
      rewrite Heq5. rewrite Zminus_mod. rewrite Hval5. rewrite Z.sub_diag. apply Z.mod_0_l. lia. }
    assert (HgcdN1N : Z.gcd (N-1) N = 1) by (unfold N; apply neg_one_gcd_pow2; exact Hn).
    assert (HgcdN1bN : Z.gcd ((N-1)^bv1) N = 1).
    { exact (Z.coprime_pow_l (N-1) N bv1 (proj1 Hb1) HgcdN1N). }
    assert (HNdvd5 : (N | (5:Z)^av1 - (5:Z)^av2)).
    { exact (Z.gauss N ((N-1)^bv1) ((5:Z)^av1 - (5:Z)^av2) HN_diff2
                     (eq_trans (Z.gcd_comm N ((N-1)^bv1)) HgcdN1bN)). }
    exact (five_pow_eq_implies_equal n Hn H2n Hn2 av1 av2 Ha1 Ha2 HNdvd5). }
  split; apply sig_eq; [exact Hav12 | exact Hbv12].
Qed.


Theorem znz_units_pow2_structure_v2 :
  forall (n : nat) (Hn : (2 <= n)%nat)
         (H2n : (1 < Nat.pow 2 n)%nat) (Hn2 : (0 < Nat.pow 2 (n-2))%nat),
    znz_units_group (Nat.pow 2 n) H2n ≅
    znz_group (Nat.pow 2 (n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1).
Proof.
  intros n Hn H2n Hn2.
  apply GroupIsomorphic_symm.
  set (N := Z.of_nat (Nat.pow 2 n)).
  set (M := Z.of_nat (Nat.pow 2 (n-2))).
  set (SrcG := znz_group (Nat.pow 2 (n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1)).
  set (TgtG := znz_units_group (Nat.pow 2 n) H2n).
  assert (HN_gt1 : 1 < N).
  { unfold N. assert ((4 <= Nat.pow 2 n)%nat)
      by (change (4%nat) with (Nat.pow 2 2); apply Nat.pow_le_mono_r; lia). lia. }
  assert (HN_pos : 0 < N) by lia.
  assert (HM_pos : 0 < M).
  { unfold M. assert ((1 <= Nat.pow 2 (n-2))%nat)
      by (apply (Nat.le_trans _ (Nat.pow 2 0) _); [simpl; lia | apply Nat.pow_le_mono_r; lia]).
    lia. }
  assert (H4N : (4 | N)).
  { unfold N. exists (Z.of_nat (Nat.pow 2 (n-2))).
    assert (H4 : (4 * Nat.pow 2 (n-2) = Nat.pow 2 n)%nat).
    { change (4%nat) with (Nat.pow 2 2). rewrite <- Nat.pow_add_r. f_equal. lia. }
    zify. lia. }
  assert (H5period : (N | (5:Z)^M - 1)).
  { unfold N, M. apply five_pow_pow2_nm2_one. exact Hn. }
  assert (HN1period : (N | (N-1)^2 - 1)).
  { apply neg_one_sq_one_pow2. exact Hn. }
  assert (H5M : (5:Z)^M mod N = 1) by (apply dvd_to_one_mod; [lia | exact H5period]).
  assert (HN12 : (N-1)^2 mod N = 1) by (apply dvd_to_one_mod; [lia | exact HN1period]).
  assert (Hgcd5N : Z.gcd 5 N = 1) by (unfold N; apply five_gcd_pow2; lia).
  assert (HgcdN1N : Z.gcd (N-1) N = 1) by (unfold N; apply neg_one_gcd_pow2; exact Hn).
  assert (Hn_pos2 : (0 < Nat.pow 2 n)%nat) by lia.
  set (phi := fun (p : carrier SrcG) =>
    let a := proj1_sig (fst p) in
    let b := proj1_sig (snd p) in
    let val := (5:Z)^a * (N-1)^b mod N in
    let Ha := proj2_sig (fst p) in
    let Hb := proj2_sig (snd p) in
    let Hval_range : 0 <= val < N := Z.mod_pos_bound _ _ HN_pos in
    let Hgcd5aN : Z.gcd ((5:Z)^a) N = 1 :=
      Z.coprime_pow_l 5 N a (proj1 Ha) Hgcd5N in
    let HgcdN1bN : Z.gcd ((N-1)^b) N = 1 :=
      Z.coprime_pow_l (N-1) N b (proj1 Hb) HgcdN1N in
    let Hgcd_prod : Z.gcd ((5:Z)^a * (N-1)^b) N = 1 :=
      znz_gcd_mul_coprime (Nat.pow 2 n) ((5:Z)^a) ((N-1)^b) Hgcd5aN HgcdN1bN in
    let Hgcd_val : Z.gcd val N = 1 :=
      eq_trans (znz_gcd_mod_eq (Nat.pow 2 n) Hn_pos2 ((5:Z)^a * (N-1)^b)) Hgcd_prod in
    (exist _ val (conj Hval_range Hgcd_val) : carrier TgtG)).
  exists phi.
  split; [| split].
  (* 1. Homomorphism *)
  - intros [a1 b1] [a2 b2].
    apply sig_eq. simpl.
    unfold phi. simpl.
    rewrite <- Z.mul_mod by lia.
    apply phi_hom_val.
    + exact HN_gt1.
    + exact HM_pos.
    + exact (proj2_sig a1).
    + exact (proj2_sig a2).
    + exact (proj2_sig b1).
    + exact (proj2_sig b2).
    + exact H5M.
    + exact HN12.
  (* 2. Injectivity *)
  - intros [a1 b1] [a2 b2] Heq.
    assert (Hval_eq : (5:Z)^(proj1_sig a1) * (N-1)^(proj1_sig b1) mod N =
                      (5:Z)^(proj1_sig a2) * (N-1)^(proj1_sig b2) mod N).
    { assert (Htmp : proj1_sig (phi (a1, b1)) = proj1_sig (phi (a2, b2)))
        by (rewrite Heq; reflexivity).
      unfold phi in Htmp. simpl in Htmp. exact Htmp. }
    destruct (phi_inj n Hn H2n Hn2 a1 a2 b1 b2 Hval_eq) as [Ha12 Hb12].
    rewrite Ha12, Hb12. reflexivity.
  (* 3. Surjectivity from equal orders *)
  - assert (HordG : GroupOrder SrcG (Nat.pow 2 (n-1))).
    { unfold SrcG.
      assert (Hord_a : GroupOrder (znz_group (Nat.pow 2 (n-2)) Hn2) (Nat.pow 2 (n-2)))
        by exact (znz_group_order_n (Nat.pow 2 (n-2)) Hn2).
      assert (Hord_b : GroupOrder (znz_group 2 (Nat.lt_0_succ 1)) 2)
        by exact (znz_group_order_n 2 (Nat.lt_0_succ 1)).
      assert (Hprod : GroupOrder (znz_group (Nat.pow 2 (n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1))
                                 (Nat.pow 2 (n-2) * 2)) by
        exact (group_order_product _ _ _ _ Hord_a Hord_b).
      assert (Heq_ord : (Nat.pow 2 (n-2) * 2 = Nat.pow 2 (n-1))%nat).
      { replace (n-1)%nat with (n-2+1)%nat by lia.
        rewrite Nat.pow_add_r. simpl. lia. }
      rewrite <- Heq_ord. exact Hprod. }
    assert (HordU : GroupOrder TgtG (Nat.pow 2 (n-1))).
    { unfold TgtG. exact (znz_units_pow2_order n Hn H2n). }
    apply (inj_hom_surj_of_eq_order SrcG TgtG (Nat.pow 2 (n-1)) phi).
    + intros [a1 b1] [a2 b2].
      apply sig_eq. simpl.
      unfold phi. simpl.
      rewrite <- Z.mul_mod by lia.
      apply phi_hom_val.
      * exact HN_gt1.
      * exact HM_pos.
      * exact (proj2_sig a1).
      * exact (proj2_sig a2).
      * exact (proj2_sig b1).
      * exact (proj2_sig b2).
      * exact H5M.
      * exact HN12.
    + intros [a1 b1] [a2 b2] Heq.
      assert (Hval_eq : (5:Z)^(proj1_sig a1) * (N-1)^(proj1_sig b1) mod N =
                        (5:Z)^(proj1_sig a2) * (N-1)^(proj1_sig b2) mod N).
      { assert (Htmp : proj1_sig (phi (a1, b1)) = proj1_sig (phi (a2, b2)))
          by (rewrite Heq; reflexivity).
        unfold phi in Htmp. simpl in Htmp. exact Htmp. }
      destruct (phi_inj n Hn H2n Hn2 a1 a2 b1 b2 Hval_eq) as [Ha12 Hb12].
      rewrite Ha12, Hb12. reflexivity.
    + exact HordG.
    + exact HordU.
Qed.
