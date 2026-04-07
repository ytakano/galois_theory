Require Import Corelib.Init.Peano Corelib.Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import ZArith ZArith.Znumtheory ZArith.Zpow_facts Init.Logic.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** 互除法の原理:
    a と b を自然数、b ≠ 0、r = a mod b とするとき、
    Nat.gcd a b = Nat.gcd b r が成り立つ。

    証明の方針:
      任意の自然数 d に対して、
        d | a かつ d | b  ⟺  d | b かつ d | (a mod b)
      が成立することを利用し、divide_antisym により等式を導く。        *)

Local Close Scope Z_scope.

Theorem gcd_euclidean : forall (a b : nat),
  b <> 0 ->
  Nat.gcd a b = Nat.gcd b (a mod b).
Proof.
  intros a b Hb.
  apply Nat.divide_antisym.
  - (* gcd(a, b) | gcd(b, a mod b) を示す *)
    apply Nat.gcd_greatest.
    + (* gcd(a, b) | b *)
      apply Nat.gcd_divide_r.
    + (* gcd(a, b) | a mod b
         mod_eq より a mod b = a - b * (a / b) なので
         gcd(a,b) | a かつ gcd(a,b) | b * (a/b) から成立 *)
      rewrite (Nat.Div0.mod_eq a b).
      apply Nat.divide_sub_r.
      * apply Nat.gcd_divide_l.
      * apply Nat.divide_mul_l.
        apply Nat.gcd_divide_r.
  - (* gcd(b, a mod b) | gcd(a, b) を示す *)
    apply Nat.gcd_greatest.
    + (* gcd(b, a mod b) | a
         div_mod より a = b * (a / b) + a mod b なので
         gcd(b, a mod b) | b かつ gcd(b, a mod b) | a mod b から成立 *)
      rewrite (Nat.div_mod a b Hb) at 2.
      apply Nat.divide_add_r.
      * apply Nat.divide_mul_l.
        apply Nat.gcd_divide_l.
      * apply Nat.gcd_divide_r.
    + (* gcd(b, a mod b) | b *)
      apply Nat.gcd_divide_l.
Qed.

Open Scope Z_scope.

(** 合同式 (Congruence):
    m を自然数、a, b を整数とするとき、
    a ≡ b (mod m) とは (a - b) が m の倍数であること、
    すなわち Z.of_nat m が a - b を割り切ることと定義する。  *)

Definition cong (m : nat) (a b : Z) : Prop :=
  (Z.of_nat m | a - b).

Notation "a ≡ b [ 'mod' m ]" := (cong m a b)
  (at level 70, b at next level, format "a  ≡  b  [ 'mod'  m ]").

(** 一次不定方程式 (Linear Diophantine Equation):
    a, b, d を整数とし、g = gcd(a, b) とするとき、次は同値:
      (1) ax + by = d を満たす整数解 (x, y) が存在する
      (2) g が d を割り切る (g ∣ d)

    証明の方針:
      (→) ax + by = d を仮定する。g | a かつ g | b より
          g | ax かつ g | by が成り立ち、g | ax + by = d を得る。
      (←) g | d を仮定する。ベズーの定理より g = ua + vb となる
          整数 u, v が存在する。d = gk と書くと、
          x₀ = uk, y₀ = vk が解となる:
          ax₀ + by₀ = (ua + vb)k = gk = d.          *)

Theorem linear_diophantine : forall (a b d : Z),
  (exists x y : Z, a * x + b * y = d) <-> (Z.gcd a b | d).
Proof.
  intros a b d.
  split.
  - (* → : 整数解 (x, y) が存在するならば g | d *)
    intros [x [y Heq]].
    rewrite <- Heq.
    apply Z.divide_add_r.
    + (* g | a より g | a*x *)
      apply Z.divide_mul_l, Z.gcd_divide_l.
    + (* g | b より g | b*y *)
      apply Z.divide_mul_l, Z.gcd_divide_r.
  - (* ← : g | d ならば整数解が存在する *)
    intros [k Hk].
    (* ベズーの定理: ∃ u v, u*a + v*b = g *)
    destruct (Zis_gcd_bezout a b (Z.gcd a b) (Zgcd_is_gcd a b)) as [u v Hbezout].
    (* x₀ = u*k, y₀ = v*k が解 *)
    exists (u * k), (v * k).
    rewrite Hk. rewrite <- Hbezout. ring.
Qed.

(** 合同式の性質 (Properties of Congruence):
    m を自然数、a, b, c, d を整数とし、
    a ≡ b [mod m] かつ c ≡ d [mod m] とする。このとき:
      1. a + c ≡ b + d [mod m]  (加法)
      2. a - c ≡ b - d [mod m]  (減法)
      3. a * c ≡ b * d [mod m]  (乗法)

    証明の方針:
      仮定は m | (a - b) および m | (c - d) と展開できる。
      1: (a+c)-(b+d) = (a-b)+(c-d) と変形し、divide_add_r を適用。
      2: (a-c)-(b-d) = (a-b)+(-(c-d)) と変形し、divide_add_r と divide_opp_r を適用。
      3: a*c-b*d = (a-b)*c + b*(c-d) と変形し、divide_add_r と divide_mul_l を適用。  *)

Theorem cong_add : forall (m : nat) (a b c d : Z),
  a ≡ b [mod m] -> c ≡ d [mod m] -> a + c ≡ b + d [mod m].
Proof.
  intros m a b c d H1 H2.
  unfold cong in *.
  replace ((a + c) - (b + d)) with ((a - b) + (c - d)) by ring.
  apply Z.divide_add_r; assumption.
Qed.

Theorem cong_sub : forall (m : nat) (a b c d : Z),
  a ≡ b [mod m] -> c ≡ d [mod m] -> a - c ≡ b - d [mod m].
Proof.
  intros m a b c d H1 H2.
  unfold cong in *.
  replace ((a - c) - (b - d)) with ((a - b) + (-(c - d))) by ring.
  apply Z.divide_add_r.
  - assumption.
  - apply Z.divide_opp_r; assumption.
Qed.

Theorem cong_mul : forall (m : nat) (a b c d : Z),
  a ≡ b [mod m] -> c ≡ d [mod m] -> a * c ≡ b * d [mod m].
Proof.
  intros m a b c d H1 H2.
  unfold cong in *.
  replace (a * c - b * d) with ((a - b) * c + b * (c - d)) by ring.
  apply Z.divide_add_r.
  - apply Z.divide_mul_l; assumption.
  - replace (b * (c - d)) with ((c - d) * b) by ring.
    apply Z.divide_mul_l; assumption.
Qed.


(** 群 (Group):
    集合 carrier と二項演算 op を持ち、以下の公理を満たす代数的構造:
      1. 結合律 (assoc)   : (a * b) * c = a * (b * c)
      2. 左単位元 (id_left)  : e * a = a
      3. 右単位元 (id_right) : a * e = a
      4. 左逆元 (inv_left)  : inv(a) * a = e
      5. 右逆元 (inv_right) : a * inv(a) = e  *)

Record Group : Type := {
  carrier : Type;           (* 台集合 *)
  op : carrier -> carrier -> carrier;  (* 二項演算 *)
  e : carrier;              (* 単位元 *)
  inv : carrier -> carrier; (* 逆元写像 *)

  assoc : forall a b c : carrier,
    op a (op b c) = op (op a b) c;

  id_left : forall a : carrier,
    op e a = a;

  id_right : forall a : carrier,
    op a e = a;

  inv_left : forall a : carrier,
    op (inv a) a = e;

  inv_right : forall a : carrier,
    op a (inv a) = e
}.

(** 群の冪乗 (Group Power):
    群 G の元 a と整数 n に対して、a の n 乗を定義する。
    - n = 0 のとき: 単位元 e
    - n > 0 のとき: a を n 回繰り返し演算する
    - n < 0 のとき: a の逆元を |n| 回繰り返し演算する  *)

Fixpoint gpow_nat (G : Group) (a : carrier G) (n : nat) : carrier G :=
  match n with
  | O => e G
  | S n' => op G a (gpow_nat G a n')
  end.

Definition gpow (G : Group) (a : carrier G) (n : Z) : carrier G :=
  match n with
  | Z0 => e G
  | Zpos p => gpow_nat G a (Pos.to_nat p)
  | Zneg p => gpow_nat G (inv G a) (Pos.to_nat p)
  end.

(** 巡回群 (Cyclic Group):
    群 G が巡回群であるとは、ある生成元 g ∈ G が存在して、
    G の任意の元 a が g の冪乗として表されることをいう:
      ∃ g, ∀ a, ∃ n : Z, gpow G g n = a

    Record として定義することで、生成元と巡回性の証明をまとめて扱う。
    `:>` による強制型変換により CyclicGroup を Group として直接使用できる。  *)

Record CyclicGroup : Type := {
  cyclic_group :> Group;
  generator : carrier cyclic_group;
  cyclic_property : forall a : carrier cyclic_group,
    exists n : Z, gpow cyclic_group generator n = a
}.

(** 群の同型 (Group Isomorphism):
    群 G1 から G2 への写像 f : carrier G1 -> carrier G2 が
    以下の条件をすべて満たすとき、f を同型写像 (isomorphism) といい、
    G1 と G2 は同型 (G1 ≅ G2) であるという:
      1. 準同型性 (homomorphism) : ∀ x y, f (op G1 x y) = op G2 (f x) (f y)
      2. 単射性 (injective)      : ∀ x y, f x = f y → x = y
      3. 全射性 (surjective)     : ∀ b, ∃ a, f a = b

    IsIsomorphism は写像 f に関する命題、
    GroupIsomorphic は二つの群の間に同型写像が存在することの命題。  *)

Definition IsIsomorphism (G1 G2 : Group)
    (f : carrier G1 -> carrier G2) : Prop :=
  (* 準同型性 *)
  (forall x y : carrier G1, f (op G1 x y) = op G2 (f x) (f y)) /\
  (* 単射性 *)
  (forall x y : carrier G1, f x = f y -> x = y) /\
  (* 全射性 *)
  (forall b : carrier G2, exists a : carrier G1, f a = b).

Definition GroupIsomorphic (G1 G2 : Group) : Prop :=
  exists f : carrier G1 -> carrier G2, IsIsomorphism G1 G2 f.

Notation "G1 ≅ G2" := (GroupIsomorphic G1 G2)
  (at level 70).

(** 群の位数 (Order of a Group):
    群 G の位数が n であるとは、台集合 carrier G から有限集合 Fin.t n への
    全単射が存在することをいう。
    言い換えると、G の元をちょうど n 個の添字で過不足なく番号づけできることである。  *)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Classical.
Import ListNotations.

Definition GroupOrder (G : Group) (n : nat) : Prop :=
  exists f : carrier G -> Fin.t n,
    (* 単射性: 異なる元は異なる添字に対応する *)
    (forall x y : carrier G, f x = f y -> x = y) /\
    (* 全射性: すべての添字に対応する元が存在する *)
    (forall i : Fin.t n, exists x : carrier G, f x = i).

(** 部分群 (Subgroup):
    群 G の部分集合 H が部分群であるとは、以下の三条件を満たすことをいう:
      1. 単位元包含 (contains_e) : e ∈ H
      2. 演算で閉じている (closed_op) : a ∈ H かつ b ∈ H ならば a * b ∈ H
      3. 逆元で閉じている (closed_inv) : a ∈ H ならば inv(a) ∈ H

    ここで H は台集合上の述語 (carrier G -> Prop) として表す。  *)

Record Subgroup (G : Group) : Type := {
  subgroup_pred : carrier G -> Prop;   (* 部分群を表す述語 *)

  contains_e : subgroup_pred (e G);

  closed_op : forall a b : carrier G,
    subgroup_pred a -> subgroup_pred b -> subgroup_pred (op G a b);

  closed_inv : forall a : carrier G,
    subgroup_pred a -> subgroup_pred (inv G a)
}.

(** 群の利用例 (Examples of Group):
    Group レコードと gpow の使い方を示す具体例。

    square: 群の二乗演算 op G x x を一般的な形で定義した補助関数。
    Z_add_group: 整数全体 (Z, +, 0, -) が Group の公理を満たす具体例。
    最後の Eval compute で、Z_add_group 上での square 3 = 6 を確認できる。  *)

Definition square (G : Group) (x : carrier G) : carrier G := op G x x.

Definition Z_add_group : Group.
Proof.
  refine {|
    carrier := Z;
    op := Z.add;
    e := 0%Z;
    inv := Z.opp
  |}.
  - intros a b c. apply Z.add_assoc.
  - intros a. apply Z.add_0_l.
  - intros a. apply Z.add_0_r.
  - intros a. apply Z.add_opp_diag_l.
  - intros a. apply Z.add_opp_diag_r.
Defined.

Eval compute in square Z_add_group 3.

(** 巡回群の利用例 (Example of CyclicGroup):
    (Z, +) は 1 を生成元とする巡回群である。
    任意の整数 a に対して gpow Z_add_group 1 a = a が成り立つ。  *)

Definition Z_cyclic_group : CyclicGroup.
Proof.
  refine {|
    cyclic_group := Z_add_group;
    generator := 1%Z
  |}.
  intros a.
  exists a.
  (* 補題1: gpow_nat Z_add_group 1 n = Z.of_nat n *)
  assert (Hpos : forall n, gpow_nat Z_add_group 1%Z n = Z.of_nat n).
  { induction n as [| n' IH].
    - reflexivity.
    - rewrite Nat2Z.inj_succ.
      cbn [gpow_nat op carrier Z_add_group]. rewrite IH. ring. }
  (* 補題2: gpow_nat Z_add_group (-1) n = - Z.of_nat n *)
  assert (Hneg : forall n, gpow_nat Z_add_group (-1)%Z n = - Z.of_nat n).
  { induction n as [| n' IH].
    - reflexivity.
    - rewrite Nat2Z.inj_succ.
      cbn [gpow_nat op carrier Z_add_group]. rewrite IH. ring. }
  unfold gpow.
  destruct a as [| p | p].
  - (* a = 0 *) reflexivity.
  - (* a = Zpos p *) rewrite Hpos. apply positive_nat_Z.
  - (* a = Zneg p *) rewrite Hneg. rewrite positive_nat_Z. reflexivity.
Defined.

Eval compute in square Z_cyclic_group 3.

(** ===========================================================
    巡回群の部分群に関する補題と定理
    =========================================================== *)

From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.ClassicalEpsilon.

(** gpow_nat の加法性:
    g^(m+n) = g^m * g^n  (自然数冪)

    証明: m に関する帰納法。
    m = 0   : g^(0+n) = g^n = e * g^n = g^0 * g^n.
    m = S m': g^(S m'+n) = g * g^(m'+n) = g * (g^m' * g^n)
                         = (g * g^m') * g^n = g^(S m') * g^n.  *)
Lemma gpow_nat_add : forall (G : Group) (a : carrier G) (m n : nat),
  gpow_nat G a (m + n) = op G (gpow_nat G a m) (gpow_nat G a n).
Proof.
  intros G a m n.
  induction m as [| m' IH].
  - simpl. symmetry. apply id_left.
  - simpl. rewrite IH. apply assoc.
Qed.

(** gpow の加法性: g^(m+n) = g^m * g^n  (整数冪)

    証明: m, n の符号による場合分け。
    (>= 0, >= 0): Pos2Nat.inj_add と gpow_nat_add を使用。
    (-, -): 逆元側の gpow_nat_add を使用。
    (>= 0, -), (-, >= 0): 正負の打ち消しが生じる場合は符号の大小で再度分岐し,
                    inv_right / inv_left と id_right / id_left を使用。  *)

Lemma gpow_of_nat :
  forall (G : Group) (a : carrier G) (k : nat),
    gpow G a (Z.of_nat k) = gpow_nat G a k.
Proof.
  intros G a [|k].
  - reflexivity.
  - simpl.
    rewrite SuccNat2Pos.id_succ.
    reflexivity.
Qed.

Lemma gpow_add_pos_pos : forall (G : Group) (a : carrier G) (m n : Z),
  n >= 0 /\ m >= 0 -> gpow G a (m + n) = op G (gpow G a m) (gpow G a n).
Proof.
  intros G a m n [Hn Hm].

  assert (Hm_nat : exists km : nat, m = Z.of_nat km).
  {
    exists (Z.to_nat m).
    symmetry.
    apply Z2Nat.id.
    lia.
  }

  assert (Hn_nat : exists kn : nat, n = Z.of_nat kn).
  {
    exists (Z.to_nat n).
    symmetry.
    apply Z2Nat.id.
    lia.
  }

  destruct Hm_nat as [km Hkm].
  destruct Hn_nat as [kn Hkn].
  subst m n.

  rewrite <- Nat2Z.inj_add.
  rewrite !gpow_of_nat.

  change (gpow_nat G a (km + kn) = op G (gpow_nat G a km) (gpow_nat G a kn)).

  rewrite <- gpow_nat_add.
  reflexivity.
Qed.


Lemma gpow_neg_of_nat :
  forall (G : Group) (a : carrier G) (k : nat),
    gpow G a (- Z.of_nat k) = gpow_nat G (inv G a) k.
Proof.
  intros G a [|k].
  - reflexivity.
  - simpl.
    rewrite SuccNat2Pos.id_succ.
    reflexivity.
Qed.

Lemma gpow_add_neg_neg : forall (G : Group) (a : carrier G) (m n : Z),
  n < 0 /\ m < 0 -> gpow G a (m + n) = op G (gpow G a m) (gpow G a n).
Proof.
  intros G a m n [Hn Hm].

  assert (Hm_nat : exists km : nat, m = - Z.of_nat km).
  {
    exists (Z.to_nat (-m)).
    rewrite Z2Nat.id by lia.
    ring.
  }

  assert (Hn_nat : exists kn : nat, n = - Z.of_nat kn).
  {
    exists (Z.to_nat (-n)).
    rewrite Z2Nat.id by lia.
    ring.
  }

  destruct Hm_nat as [km Hkm].
  destruct Hn_nat as [kn Hkn].
  subst m n.

  replace (- Z.of_nat km + - Z.of_nat kn) with (- Z.of_nat (km + kn))
    by (rewrite Nat2Z.inj_add; ring).
  rewrite !gpow_neg_of_nat.
  rewrite <- gpow_nat_add.
  reflexivity.
Qed.

(** a は自身の冪と可換: a * a^n = a^n * a

    証明: n に関する帰納法。
    n = 0  : a * e = e * a (どちらも a).
    n = S n': a * (a * a^n') = a * (a^n' * a) [IH]
                             = (a * a^n') * a  [assoc].  *)
Lemma gpow_nat_comm : forall (G : Group) (a : carrier G) (n : nat),
  op G a (gpow_nat G a n) = op G (gpow_nat G a n) a.
Proof.
  intros G a n.
  induction n as [| n' IH].
  - simpl. rewrite id_right. symmetry. apply id_left.
  - simpl. rewrite <- assoc. f_equal. exact IH.
Qed.

(** 単位元の逆元は単位元: inv(e) = e  *)
Lemma inv_e : forall (G : Group), inv G (e G) = e G.
Proof.
  intro G.
  rewrite <- (id_left G (inv G (e G))). apply inv_right.
Qed.

(** 右逆元の一意性: x * y = e → y = inv(x)  *)
Lemma inv_unique_r : forall (G : Group) (x y : carrier G),
  op G x y = e G -> y = inv G x.
Proof.
  intros G x y H.
  rewrite <- (id_left G y).
  rewrite <- (inv_left G x).
  rewrite <- assoc.
  rewrite H.
  apply id_right.
Qed.

(** 積の逆元: inv(a * b) = inv(b) * inv(a)  *)
Lemma inv_op : forall (G : Group) (a b : carrier G),
  inv G (op G a b) = op G (inv G b) (inv G a).
Proof.
  intros G a b.
  symmetry. apply inv_unique_r.
  rewrite assoc.
  rewrite <- (assoc G a b (inv G b)).
  rewrite inv_right.
  rewrite id_right.
  apply inv_right.
Qed.

(** 逆元の冪: (inv a)^n = inv(a^n)

    証明: n に関する帰納法。
    n = 0  : inv(e) = e [inv_e].
    n = S n': inv(a) * inv(a^n') = inv(a^n' * a) [inv_op]
                                 = inv(a * a^n')  [gpow_nat_comm]
                                 = inv(a^(S n')).  *)
Lemma gpow_nat_inv_eq : forall (G : Group) (a : carrier G) (n : nat),
  gpow_nat G (inv G a) n = inv G (gpow_nat G a n).
Proof.
  intros G a n.
  induction n as [| n' IH].
  - simpl. symmetry. apply inv_e.
  - simpl. rewrite IH.
    rewrite <- (inv_op G (gpow_nat G a n') a).
    f_equal. simpl. symmetry. apply gpow_nat_comm.
Qed.

(** gpow の加法性 (正 + 負の場合):
    g^(m+n) = g^m * g^n  (m >= 0, n < 0)

    証明: m = Z.of_nat km, n = - Z.of_nat kn と置き,
    kn <= km の場合と km < kn の場合に分岐する.

    Case 1 (kn <= km, m+n >= 0):
      g^(km-kn) = g^((km-kn)+kn) * (g^{-1})^kn を gpow_nat_add で展開し,
      g^kn * (g^{-1})^kn = e (inv_right) を使って右辺を消去する.

    Case 2 (km < kn, m+n < 0):
      (g^{-1})^(kn-km) = g^km * (g^{-1})^(km+(kn-km)) を gpow_nat_add で展開し,
      g^km * (g^{-1})^km = e (inv_right) を使って右辺を消去する.  *)
Lemma gpow_add_pos_neg : forall (G : Group) (a : carrier G) (m n : Z),
  n < 0 /\ m >= 0 -> gpow G a (m + n) = op G (gpow G a m) (gpow G a n).
Proof.
  intros G a m n [Hn Hm].

  assert (Hm_nat : exists km : nat, m = Z.of_nat km).
  { exists (Z.to_nat m). symmetry. apply Z2Nat.id. lia. }

  assert (Hn_nat : exists kn : nat, n = - Z.of_nat kn).
  { exists (Z.to_nat (-n)). rewrite Z2Nat.id by lia. ring. }

  destruct Hm_nat as [km Hkm].
  destruct Hn_nat as [kn Hkn].
  subst m n.

  destruct (Nat.le_gt_cases kn km) as [Hle | Hlt].
  - (* Case 1: kn <= km, よって m + n >= 0 *)
    replace (Z.of_nat km + - Z.of_nat kn) with (Z.of_nat (km - kn))
      by (rewrite Nat2Z.inj_sub by lia; ring).
    rewrite gpow_of_nat, gpow_of_nat, gpow_neg_of_nat.
    (* 目標: gpow_nat G a (km - kn) = op G (gpow_nat G a km) (gpow_nat G (inv G a) kn) *)
    replace km with (km - kn + kn)%nat at 2 by lia.
    rewrite gpow_nat_add, <- assoc, (gpow_nat_inv_eq G a kn), inv_right, id_right.
    reflexivity.
  - (* Case 2: km < kn, よって m + n < 0 *)
    replace (Z.of_nat km + - Z.of_nat kn) with (- Z.of_nat (kn - km))
      by (rewrite Nat2Z.inj_sub by lia; ring).
    rewrite gpow_of_nat, gpow_neg_of_nat, gpow_neg_of_nat.
    (* 目標: gpow_nat G (inv G a) (kn - km) = op G (gpow_nat G a km) (gpow_nat G (inv G a) kn) *)
    replace kn with (km + (kn - km))%nat at 2 by lia.
    rewrite gpow_nat_add, assoc, (gpow_nat_inv_eq G a km), inv_right, id_left.
    reflexivity.
Qed.

(** gpow の加法性 (負 + 正の場合):
    g^(m+n) = g^m * g^n  (m < 0, n >= 0)

    証明: m = - Z.of_nat km, n = Z.of_nat kn と置き,
    km <= kn の場合と kn < km の場合に分岐する.

    Case 1 (km <= kn, m+n >= 0):
      g^(kn-km) = (g^{-1})^km * g^(km+(kn-km)) を gpow_nat_add で展開し,
      (g^{-1})^km * g^km = e (inv_left) を使って左辺を消去する.

    Case 2 (kn < km, m+n < 0):
      (g^{-1})^(km-kn) = (g^{-1})^((km-kn)+kn) * g^kn を gpow_nat_add で展開し,
      (g^{-1})^kn * g^kn = e (inv_left) を使って右辺を消去する.  *)
Lemma gpow_add_neg_pos : forall (G : Group) (a : carrier G) (m n : Z),
  n >= 0 /\ m < 0 -> gpow G a (m + n) = op G (gpow G a m) (gpow G a n).
Proof.
  intros G a m n [Hn Hm].

  assert (Hm_nat : exists km : nat, m = - Z.of_nat km).
  { exists (Z.to_nat (-m)). rewrite Z2Nat.id by lia. ring. }

  assert (Hn_nat : exists kn : nat, n = Z.of_nat kn).
  { exists (Z.to_nat n). symmetry. apply Z2Nat.id. lia. }

  destruct Hm_nat as [km Hkm].
  destruct Hn_nat as [kn Hkn].
  subst m n.

  destruct (Nat.le_gt_cases km kn) as [Hle | Hlt].
  - (* Case 1: km <= kn, よって m + n >= 0 *)
    replace (- Z.of_nat km + Z.of_nat kn) with (Z.of_nat (kn - km))
      by (rewrite Nat2Z.inj_sub by lia; ring).
    rewrite gpow_of_nat, gpow_neg_of_nat, gpow_of_nat.
    (* 目標: gpow_nat G a (kn - km) = op G (gpow_nat G (inv G a) km) (gpow_nat G a kn) *)
    replace kn with (km + (kn - km))%nat at 2 by lia.
    rewrite gpow_nat_add, assoc, (gpow_nat_inv_eq G a km), inv_left, id_left.
    reflexivity.
  - (* Case 2: kn < km, よって m + n < 0 *)
    replace (- Z.of_nat km + Z.of_nat kn) with (- Z.of_nat (km - kn))
      by (rewrite Nat2Z.inj_sub by lia; ring).
    rewrite gpow_neg_of_nat, gpow_neg_of_nat, gpow_of_nat.
    (* 目標: gpow_nat G (inv G a) (km - kn) = op G (gpow_nat G (inv G a) km) (gpow_nat G a kn) *)
    replace km with ((km - kn) + kn)%nat at 2 by lia.
    rewrite gpow_nat_add, <- assoc, (gpow_nat_inv_eq G a kn), inv_left, id_right.
    reflexivity.
Qed.

Lemma gpow_add : forall (G : Group) (a : carrier G) (m n : Z),
  gpow G a (m + n) = op G (gpow G a m) (gpow G a n).
Proof.
  intros G a m n.
  destruct (Z.lt_ge_cases m 0) as [Hm | Hm], (Z.lt_ge_cases n 0) as [Hn | Hn].
  - (* m < 0, n < 0 *)
    apply gpow_add_neg_neg. lia.
  - (* m < 0, n >= 0 *)
    apply gpow_add_neg_pos. lia.
  - (* m >= 0, n < 0 *)
    apply gpow_add_pos_neg. lia.
  - (* m >= 0, n >= 0 *)
    apply gpow_add_pos_pos. lia.
Qed.


(** 逆元の逆元は元自身: inv(inv(a)) = a  *)
Lemma inv_inv : forall (G : Group) (a : carrier G), inv G (inv G a) = a.
Proof.
  intros G a.
  rewrite <- (id_right G (inv G (inv G a))).
  rewrite <- (inv_left G a).
  rewrite assoc.
  rewrite inv_left.
  apply id_left.
Qed.

(** 単位元の冪: e^n = e  *)
Lemma gpow_nat_e : forall (G : Group) (n : nat),
  gpow_nat G (e G) n = e G.
Proof.
  intros G n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. apply id_left.
Qed.

(** 整数冪における単位元: e^n = e (整数 n に対して)

    証明: n の符号による場合分け。
    n = 0  : 定義より e G.
    n > 0  : gpow_nat_e を適用。
    n < 0  : inv(e) = e を使って gpow_nat_e を適用。  *)
Lemma gpow_e : forall (G : Group) (n : Z),
  gpow G (e G) n = e G.
Proof.
  intros G n.
  destruct n as [|p|p]; simpl.
  - reflexivity.
  - apply gpow_nat_e.
  - rewrite inv_e. apply gpow_nat_e.
Qed.

(** 自然数冪の乗法性: a^(m*n) = (a^m)^n

    証明: n に関する帰納法。
    n = 0  : a^0 = e = (a^m)^0.
    n = S n': a^(m*n' + m) = a^(m*n') * a^m [gpow_nat_add]
                           = (a^m)^n' * a^m  [IH]
                           = a^m * (a^m)^n'  [gpow_nat_comm]
                           = (a^m)^(S n').   *)
Lemma gpow_nat_mul : forall (G : Group) (a : carrier G) (m n : nat),
  gpow_nat G a (m * n) = gpow_nat G (gpow_nat G a m) n.
Proof.
  intros G a m n.
  induction n as [| n' IH].
  - rewrite Nat.mul_0_r. simpl. reflexivity.
  - rewrite Nat.mul_succ_r.
    rewrite gpow_nat_add.
    rewrite IH.
    simpl. symmetry. apply gpow_nat_comm.
Qed.

(** gpow の整数倍: g^(m*n) = (g^m)^n

    証明: m, n の符号による場合分けと gpow_nat_mul を使用。
    (+,+): gpow_nat_mul を直接適用。
    (+,-): gpow_nat_inv_eq で inv を外に出してから gpow_nat_mul。
    (-,+): inv a に gpow_nat_mul を適用。
    (-,-): gpow_nat_inv_eq と inv_inv で inv inv a = a に帰着。  *)
Lemma gpow_mul : forall (G : Group) (a : carrier G) (m n : Z),
  gpow G a (m * n) = gpow G (gpow G a m) n.
Proof.
  intros G a m n.
  destruct m as [| p | p], n as [| q | q]; simpl.
  - reflexivity.
  - symmetry. apply gpow_nat_e.
  - rewrite inv_e. symmetry. apply gpow_nat_e.
  - reflexivity.
  - rewrite Pos2Nat.inj_mul. apply gpow_nat_mul.
  - rewrite Pos2Nat.inj_mul.
    rewrite <- (gpow_nat_inv_eq G a (Pos.to_nat p)).
    apply gpow_nat_mul.
  - reflexivity.
  - rewrite Pos2Nat.inj_mul. apply gpow_nat_mul.
  - rewrite Pos2Nat.inj_mul.
    rewrite <- (gpow_nat_inv_eq G (inv G a) (Pos.to_nat p)).
    rewrite inv_inv.
    apply gpow_nat_mul.
Qed.

(** ===========================================================
    generator_order の証明のための補題群
    =========================================================== *)

(** 左消去則: x * y = x * z → y = z

    証明: 両辺の左から inv(x) を掛け,
    結合律・左逆元・左単位元を順に適用する.  *)
Lemma op_cancel_l : forall (G : Group) (x y z : carrier G),
  op G x y = op G x z -> y = z.
Proof.
  intros G x y z H.
  assert (key : op G (inv G x) (op G x y) = op G (inv G x) (op G x z))
    by (rewrite H; reflexivity).
  rewrite assoc, inv_left, id_left in key.
  rewrite assoc, inv_left, id_left in key.
  exact key.
Qed.

(** 等しい冪から周期を導く: i < j かつ g^i = g^j ならば g^(j-i) = e.

    証明: g^(j-i) = e を示すため, 両辺の左から g^i を掛ける.
      左辺: g^i * g^(j-i) = g^(i+(j-i)) = g^j = g^i  (仮定より)
      右辺: g^i * e = g^i
    よって op_cancel_l により g^(j-i) = e.  *)
Lemma equal_powers_imply_period :
  forall (G : Group) (a : carrier G) (i j : nat),
    (i < j)%nat ->
    gpow G a (Z.of_nat i) = gpow G a (Z.of_nat j) ->
    gpow G a (Z.of_nat (j - i)) = e G.
Proof.
  intros G a i j Hij Heq.
  apply (op_cancel_l G (gpow G a (Z.of_nat i))).
  rewrite id_right.
  rewrite <- gpow_add.
  replace (Z.of_nat i + Z.of_nat (j - i)) with (Z.of_nat j)
    by (rewrite Nat2Z.inj_sub by lia; ring).
  symmetry. exact Heq.
Qed.

(** 周期の倍数は単位元: g^d = e ならば g^(q*d) = e

    証明: Z.of_nat (q * d) = Z.of_nat d * Z.of_nat q と変形し,
    gpow_mul で g^(d*q) = (g^d)^q に変換する.
    仮定 g^d = e を代入すると e^q = e (gpow_e) となる.  *)
Lemma gpow_period_multiple :
  forall (G : Group) (a : carrier G) (d q : nat),
    gpow G a (Z.of_nat d) = e G ->
    gpow G a (Z.of_nat (q * d)) = e G.
Proof.
  intros G a d q Hd.
  replace (Z.of_nat (q * d)) with (Z.of_nat d * Z.of_nat q)
    by (rewrite Nat2Z.inj_mul; ring).
  rewrite gpow_mul, Hd.
  apply gpow_e.
Qed.

(** ===========================================================
    pigeonhole_Fin の証明のための補助定理群
    =========================================================== *)

(** Fin.t m の全要素をリストにする関数.

    fin_all 0 = []
    fin_all (S m) = F1 :: map FS (fin_all m)
    長さ = m, 重複なし, すべての要素を含む.  *)
Fixpoint fin_all (m : nat) : list (Fin.t m) :=
  match m with
  | O    => []
  | S m' => Fin.F1 :: List.map Fin.FS (fin_all m')
  end.

(** fin_all の長さは m に等しい.  *)
Lemma fin_all_length : forall m : nat,
  length (fin_all m) = m.
Proof.
  induction m as [| m' IH]; simpl.
  - reflexivity.
  - rewrite List.map_length. rewrite IH. reflexivity.
Qed.

(** fin_all m はすべての Fin.t m の要素を含む.  *)
Lemma fin_all_complete : forall (m : nat) (x : Fin.t m),
  List.In x (fin_all m).
Proof.
  intros m x.
  induction x as [m' | m' x' IHx].
  - simpl. left. reflexivity.
  - simpl. right. apply List.in_map. exact IHx.
Qed.

(** fin_all m は重複なし (NoDup).

    証明: F1 は map FS (...) に含まれない (FS の像は F1 を含まない).
    map FS は FS が単射なので NoDup を保つ (NoDup_map_NoDup_ForallPairs).  *)
Lemma fin_all_NoDup : forall m : nat,
  List.NoDup (fin_all m).
Proof.
  induction m as [| m' IH]; simpl.
  - constructor.
  - apply List.NoDup_cons.
    + intro Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [y [Heq _]].
      discriminate Heq.
    + apply List.NoDup_map_NoDup_ForallPairs.
      * intros a b _ _ H. exact (Fin.FS_inj a b H).
      * exact IH.
Qed.

(** NoDup でないリストには重複するインデックスが存在する.

    証明: リストに対する帰納法.
    先頭要素 h が tail に含まれる場合は位置 0 と S k を返す.
    h が tail にない場合は tail 自体が NoDup でなく, IH を適用.  *)
Lemma not_NoDup_has_dup : forall (A : Type) (l : list A),
  ~ List.NoDup l ->
  exists i j : nat,
    (i < j)%nat /\ (j < length l)%nat /\
    List.nth_error l i = List.nth_error l j.
Proof.
  intros A l.
  induction l as [| h t IH]; intro Hnd.
  - exfalso. apply Hnd. constructor.
  - destruct (classic (List.In h t)) as [Hin | Hnotin].
    + apply List.In_nth_error in Hin.
      destruct Hin as [k Hk].
      exists 0%nat, (S k).
      split. { lia. }
      split.
      * simpl. apply Nat.lt_succ_r.
        apply List.nth_error_Some. rewrite Hk. discriminate.
      * simpl. rewrite Hk. reflexivity.
    + assert (Hnd_t : ~ List.NoDup t).
      { intro Ht. apply Hnd. constructor; assumption. }
      destruct (IH Hnd_t) as [i [j [Hij [Hjlen Heq]]]].
      exists (S i), (S j).
      split. { lia. }
      split. { simpl. lia. }
      simpl. exact Heq.
Qed.

(** 単射 Fin.t m -> Fin.t d が存在するなら m ≤ d.

    証明: fin_all m (長さ m, NoDup) の像 map phi (fin_all m) は
    NoDup (phi が単射) かつ fin_all d に含まれる.
    List.NoDup_incl_length より length m ≤ length d.  *)
Lemma Fin_injective_le : forall (m d : nat) (phi : Fin.t m -> Fin.t d),
  (forall i j : Fin.t m, phi i = phi j -> i = j) ->
  (m <= d)%nat.
Proof.
  intros m d phi Hinj.
  assert (Hnd : List.NoDup (List.map phi (fin_all m))).
  { apply List.NoDup_map_NoDup_ForallPairs.
    - intros a b _ _ H. exact (Hinj a b H).
    - apply fin_all_NoDup. }
  assert (Hincl : List.incl (List.map phi (fin_all m)) (fin_all d)).
  { intros x _. apply fin_all_complete. }
  pose proof (List.NoDup_incl_length Hnd Hincl) as Hle.
  rewrite List.map_length, fin_all_length, fin_all_length in Hle.
  exact Hle.
Qed.

(** 鳩ノ巣原理 (有限版): h 0,...,h m は Fin.t m の m+1 個の値なので重複がある.

    証明:
    pow_seq := map h (seq 0 (S m)) は長さ m+1 のリスト.
    もし NoDup なら fin_all m (長さ m) への incl が成立し m+1 ≤ m で矛盾.
    よって NoDup でなく, not_NoDup_has_dup で重複インデックス i < j が得られる.
    nth_error_seq と nth_error_map で h i = h j を導く.  *)
Lemma pigeonhole_Fin : forall (m : nat) (h : nat -> Fin.t m),
  exists i j : nat, (i < j)%nat /\ (j <= m)%nat /\ h i = h j.
Proof.
  intros m h.
  set (pow_seq := List.map h (List.seq 0 (S m))).
  (* pow_seq の長さは m+1 *)
  assert (Hlen : length pow_seq = S m).
  { unfold pow_seq. rewrite List.map_length, List.length_seq. reflexivity. }
  (* pow_seq の nth_error k = Some (h k) for k <= m *)
  assert (Hnth : forall k, (k <= m)%nat ->
    List.nth_error pow_seq k = Some (h k)).
  { intros k Hk.
    unfold pow_seq.
    rewrite List.nth_error_map.
    rewrite List.nth_error_seq.
    assert (Hlt : Nat.ltb k (S m) = true).
    { apply Nat.ltb_lt. lia. }
    rewrite Hlt. simpl. reflexivity. }
  (* pow_seq が NoDup なら長さ ≤ m, 矛盾 *)
  destruct (classic (List.NoDup pow_seq)) as [Hnd | Hnotnd].
  - exfalso.
    pose proof (List.NoDup_incl_length Hnd
      (fun x _ => fin_all_complete m x)) as Hle.
    (* Hle : length pow_seq <= length (fin_all m) *)
    rewrite fin_all_length in Hle.
    rewrite Hlen in Hle. lia.
  - (* NoDup でないので重複インデックスが存在する *)
    destruct (not_NoDup_has_dup _ pow_seq Hnotnd) as [i [j [Hij [Hjlen Heq]]]].
    exists i, j.
    split. { exact Hij. }
    (* j <= m を導く: j < length pow_seq = S m なので j <= m *)
    assert (Hjm : (j <= m)%nat).
    { rewrite Hlen in Hjlen. lia. }
    split. { exact Hjm. }
    (* h i = h j を導く: nth_error pow_seq k = Some (h k) *)
    assert (Him : (i <= m)%nat) by lia.
    rewrite Hnth in Heq by exact Him.
    rewrite Hnth in Heq by exact Hjm.
    injection Heq. intro H. exact H.
Qed.

(** 鳩ノ巣原理 (群の冪版): 単射 f で位数 m の群を Fin.t m に写すとき,
    g^0,...,g^m の中に重複がある.

    証明: h k := f (g^k) とおくと h : nat -> Fin.t m.
    pigeonhole_Fin で i < j ≤ m, h i = h j を得る.
    f の単射性から g^i = g^j.  *)
Lemma pigeonhole_powers : forall (C : CyclicGroup) (m : nat)
    (f : carrier C -> Fin.t m),
    (forall x y : carrier C, f x = f y -> x = y) ->
    exists i j : nat,
      (i < j)%nat /\ (j <= m)%nat /\
      gpow C (generator C) (Z.of_nat i) = gpow C (generator C) (Z.of_nat j).
Proof.
  intros C m f Hinj.
  set (h := fun k => f (gpow C (generator C) (Z.of_nat k))).
  destruct (pigeonhole_Fin m h) as [i [j [Hij [Hjm Heqh]]]].
  exists i, j.
  split. { exact Hij. }
  split. { exact Hjm. }
  apply Hinj. exact Heqh.
Qed.

(** 整数冪を自然数余りに落とす補題.

    g^d = e ならば任意の x について x = g^r (r < d, r : nat) と表せる.

    証明:
    cyclic_property より x = g^z (z : Z).
    z = (z / d) * d + (z mod d).
    g^z = g^((z/d)*d + (z mod d))
        = g^((z/d)*d) * g^(z mod d)     [gpow_add]
        = (g^d)^(z/d) * g^(z mod d)     [gpow_mul]
        = e^(z/d) * g^(z mod d)          [g^d = e]
        = e * g^(z mod d)                [gpow_e]
        = g^(z mod d)                    [id_left]
    Z.mod_pos_bound より 0 ≤ z mod d < d.
    r := Z.to_nat (z mod d) とすると r < d かつ x = g^(Z.of_nat r).  *)
Lemma gpow_reduce_mod :
  forall (C : CyclicGroup) (d : nat),
    (0 < d)%nat ->
    gpow C (generator C) (Z.of_nat d) = e C ->
    forall x : carrier C,
      exists r : nat, (r < d)%nat /\
        x = gpow C (generator C) (Z.of_nat r).
Proof.
  intros C d Hd_pos Hperiod x.
  destruct (cyclic_property C x) as [z Hz].
  (* z = (z/d)*d + (z mod d) *)
  set (q := z / Z.of_nat d).
  set (r_Z := z mod Z.of_nat d).
  assert (Hdiv : z = Z.of_nat d * q + r_Z).
  { unfold q, r_Z. rewrite <- Z.div_mod. reflexivity. lia. }
  assert (Hrbound : 0 <= r_Z < Z.of_nat d).
  { unfold r_Z. apply Z.mod_pos_bound. lia. }
  set (r := Z.to_nat r_Z).
  exists r.
  split.
  - (* r < d *)
    unfold r. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
  - (* x = g^r *)
    rewrite <- Hz.
    rewrite Hdiv.
    rewrite gpow_add.
    (* g^(d*q) * g^r_Z *)
    replace (Z.of_nat d * q) with (Z.of_nat d * q) by reflexivity.
    rewrite gpow_mul.
    rewrite Hperiod.
    rewrite gpow_e.
    rewrite id_left.
    (* g^r_Z = g^(Z.of_nat r) *)
    unfold r. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(** 群の位数は周期以下: g^d = e ならば m ≤ d.

    証明:
    gpow_reduce_mod より 全元は g^0,...,g^(d-1) で表せる.
    リスト L := map (fun r => f(g^r)) (seq 0 d) は長さ d.
    fin_all m ⊆ L (各 i : Fin.t m に対して f の全射性と gpow_reduce_mod より).
    NoDup_incl_length で m ≤ d.  *)
Lemma cyclic_group_order_le_period :
  forall (C : CyclicGroup) (m d : nat),
    GroupOrder C m ->
    (0 < d)%nat ->
    gpow C (generator C) (Z.of_nat d) = e C ->
    (m <= d)%nat.
Proof.
  intros C m d Hord Hd_pos Hperiod.
  destruct Hord as [f [Hinj Hsurj]].
  (* L := [f(g^0); f(g^1); ...; f(g^(d-1))], 長さ d *)
  set (L := List.map (fun r => f (gpow C (generator C) (Z.of_nat r))) (List.seq 0 d)).
  assert (HLlen : length L = d).
  { unfold L. rewrite List.map_length, List.length_seq. reflexivity. }
  (* fin_all m ⊆ L *)
  assert (Hincl : List.incl (fin_all m) L).
  { intros i _.
    (* f の全射性より: exists x, f x = i *)
    destruct (Hsurj i) as [x Hfx].
    (* gpow_reduce_mod より: exists r < d, x = g^r *)
    destruct (gpow_reduce_mod C d Hd_pos Hperiod x) as [r [Hr Hrx]].
    (* i = f x = f(g^r) ∈ L *)
    unfold L.
    apply List.in_map_iff.
    exists r. split.
    - rewrite <- Hrx. exact Hfx.
    - apply List.in_seq. lia. }
  (* NoDup_incl_length で m ≤ d *)
  pose proof (List.NoDup_incl_length (fin_all_NoDup m) Hincl) as Hle.
  rewrite fin_all_length, HLlen in Hle.
  exact Hle.
Qed.

(** ===========================================================
    GroupOrder から全単射を取り出す補題 (unpack 用).
    =========================================================== *)

(** GroupOrder G n の定義は「carrier G → Fin.t n の全単射が存在する」なので,
    単純に destruct して成分を返す.  *)
Lemma group_order_bijection : forall (G : Group) (n : nat),
  GroupOrder G n ->
  exists f : carrier G -> Fin.t n,
    (forall x y : carrier G, f x = f y -> x = y) /\
    (forall i : Fin.t n, exists x : carrier G, f x = i).
Proof.
  intros G n [f [Hinj Hsurj]].
  exists f. split; assumption.
Qed.

(** 生成元の位数: 位数 m の巡回群 C の生成元 g に対して g^m = e.

    証明方針:
      G の位数が m であれば, 全単射 f : carrier G → Fin.t m が存在する.
      g^0, g^1, ..., g^(m-1) はすべて異なる (単射性より).
      g^m ≠ e と仮定すると m+1 個の相異なる元が存在し全単射に矛盾.
      よって g^m = e.  *)
Lemma generator_order : forall (C : CyclicGroup) (m : nat),
  GroupOrder C m ->
  gpow C (generator C) (Z.of_nat m) = e C.
Proof.
  intros C m Hord.
  (* 全単射 f : carrier C → Fin.t m を取り出す *)
  destruct (group_order_bijection C m Hord) as [f [Hinj Hsurj]].
  (* 鳩ノ巣: g^0,...,g^m の中に重複 i < j ≤ m, g^i = g^j *)
  destruct (pigeonhole_powers C m f Hinj) as [i [j [Hij_lt [Hj_le Heqpow]]]].
  (* 周期 d := j - i が 0 < d ≤ m かつ g^d = e *)
  set (d := (j - i)%nat).
  assert (Hd_pos  : (0 < d)%nat) by (unfold d; lia).
  assert (Hd_le_m : (d <= m)%nat) by (unfold d; lia).
  assert (Hd_period : gpow C (generator C) (Z.of_nat d) = e C).
  { unfold d. apply equal_powers_imply_period with (i := i) (j := j).
    - exact Hij_lt.
    - exact Heqpow. }
  (* 巡回性より m ≤ d *)
  assert (Hm_le_d : (m <= d)%nat).
  { apply cyclic_group_order_le_period with (C := C) (m := m) (d := d).
    - exact Hord.
    - exact Hd_pos.
    - exact Hd_period. }
  (* d = m なので g^m = e *)
  assert (Hd_eq_m : d = m) by lia.
  rewrite Hd_eq_m in Hd_period. exact Hd_period.
Qed.

(** シグマ型の等号 (proof_irrelevance を使用):
    命題 P が一意であるとき,
    第一成分が等しいシグマ型の要素は等しい.  *)
Lemma sig_eq : forall (A : Type) (P : A -> Prop)
    (u v : { x : A | P x }),
  proj1_sig u = proj1_sig v -> u = v.
Proof.
  intros A P [x Hx] [y Hy] Heq. simpl in Heq. subst.
  f_equal. apply proof_irrelevance.
Qed.

(** 部分群の群構造:
    G の部分群 H に群構造を与える.
    台集合は { x : carrier G | x ∈ H } とし,
    演算・単位元・逆元は G のものを H に制限して定義する.  *)
Definition subgroup_group (G : Group) (H : Subgroup G) : Group.
Proof.
  refine {|
    carrier := { x : carrier G | subgroup_pred G H x };
    op      := fun a b =>
                 exist _ (op G (proj1_sig a) (proj1_sig b))
                         (closed_op G H _ _ (proj2_sig a) (proj2_sig b));
    e       := exist _ (e G) (contains_e G H);
    inv     := fun a =>
                 exist _ (inv G (proj1_sig a))
                         (closed_inv G H _ (proj2_sig a))
  |}.
  - intros a b c. apply sig_eq. simpl. apply assoc.
  - intros a. apply sig_eq. simpl. apply id_left.
  - intros a. apply sig_eq. simpl. apply id_right.
  - intros a. apply sig_eq. simpl. apply inv_left.
  - intros a. apply sig_eq. simpl. apply inv_right.
Defined.

(** 自然数冪が部分群に属す *)
Lemma gpow_nat_in_subgroup :
  forall (G : Group) (H : Subgroup G) (x : carrier G),
    subgroup_pred G H x ->
    forall n : nat, subgroup_pred G H (gpow_nat G x n).
Proof.
  intros G H x Hx n.
  induction n as [|k IH].
  - simpl. apply contains_e.
  - simpl. apply closed_op; [exact Hx | exact IH].
Qed.

(** 整数冪が部分群に属す *)
Lemma gpow_in_subgroup :
  forall (G : Group) (H : Subgroup G) (x : carrier G),
    subgroup_pred G H x ->
    forall n : Z, subgroup_pred G H (gpow G x n).
Proof.
  intros G H x Hx n.
  destruct n as [|p|p].
  - simpl. apply contains_e.
  - simpl. apply gpow_nat_in_subgroup. exact Hx.
  - simpl. apply gpow_nat_in_subgroup. apply closed_inv. exact Hx.
Qed.

(** 群の位数は正 *)
Lemma group_order_pos :
  forall (G : Group) (m : nat),
    GroupOrder G m -> (0 < m)%nat.
Proof.
  intros G m [f [Hinj Hsurj]].
  destruct m as [|m'].
  - exfalso. apply (Fin.case0 (fun _ => False)). exact (f (e G)).
  - lia.
Qed.

(** 整列原理 *)
Lemma well_ordering_nat :
  forall (P : nat -> Prop),
    (exists n, P n) ->
    exists d, P d /\ forall k, (k < d)%nat -> ~ P k.
Proof.
  intros P Hex.
  assert (key : forall n, P n ->
    exists d, (d <= n)%nat /\ P d /\ forall k, (k < d)%nat -> ~ P k).
  { induction n as [n IH] using lt_wf_ind.
    intros Hn.
    destruct (classic (exists k, (k < n)%nat /\ P k)) as [[k [Hk HPk]] | Hno].
    - destruct (IH k Hk HPk) as [d [Hd1 [Hd2 Hd3]]].
      exists d. split. lia. split; assumption.
    - exists n. split. lia. split.
      + exact Hn.
      + intros k Hk HPk. apply Hno. exists k. split; assumption. }
  destruct Hex as [n Hn].
  destruct (key n Hn) as [d [_ [HPd Hmin]]].
  exists d. split; assumption.
Qed.

(** 生成元の自然数冪が e ならば m | k *)
Lemma generator_period_divides_nat :
  forall (C : CyclicGroup) (m k : nat),
    GroupOrder C m ->
    gpow C (generator C) (Z.of_nat k) = e C ->
    Nat.divide m k.
Proof.
  intros C m k Hord Hgk.
  assert (Hm_pos : (0 < m)%nat) by (apply group_order_pos with (G := C); exact Hord).
  set (q := (k / m)%nat).
  set (r := (k mod m)%nat).
  assert (Hdivmod : (k = q * m + r)%nat).
  { unfold q, r. pose proof (Nat.div_mod k m ltac:(lia)). lia. }
  assert (Hr_lt : (r < m)%nat).
  { unfold r. apply Nat.mod_upper_bound. lia. }
  assert (Hgr : gpow C (generator C) (Z.of_nat r) = e C).
  {
    apply (op_cancel_l C (gpow C (generator C) (Z.of_nat (q * m)))).
    rewrite id_right.
    rewrite <- gpow_add.
    replace (Z.of_nat (q * m) + Z.of_nat r) with (Z.of_nat k)
      by (rewrite <- Nat2Z.inj_add; f_equal; lia).
    rewrite Hgk.
    symmetry.
    apply gpow_period_multiple.
    apply generator_order. exact Hord.
  }
  destruct (Nat.eq_dec r 0) as [Hr0 | Hr_ne].
  - subst r. exists q. lia.
  - exfalso.
    assert (Hrpos : (0 < r)%nat) by lia.
    assert (Hm_le_r : (m <= r)%nat).
    { apply cyclic_group_order_le_period with (C := C) (m := m) (d := r).
      exact Hord. exact Hrpos. exact Hgr. }
    lia.
Qed.

(** 最小周期の存在 *)
Lemma min_period_in_subgroup :
  forall (C : CyclicGroup) (m : nat) (H : Subgroup C),
    GroupOrder C m ->
    exists d : nat,
      (0 < d)%nat /\
      subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) /\
      forall k : nat,
        (0 < k)%nat ->
        subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
        (d <= k)%nat.
Proof.
  intros C m H Hord.
  set (P := fun n => (0 < n)%nat /\ subgroup_pred C H (gpow C (generator C) (Z.of_nat n))).
  assert (HPm : P m).
  {
    unfold P. split.
    - apply group_order_pos with (G := C). exact Hord.
    - rewrite generator_order by exact Hord.
      apply contains_e.
  }
  destruct (well_ordering_nat P (ex_intro _ m HPm)) as [d [[Hd_pos Hd_in] Hd_min]].
  exists d. split. exact Hd_pos. split. exact Hd_in.
  intros k Hk_pos Hk_in.
  destruct (Nat.lt_ge_cases k d) as [Hlt | Hge].
  - exfalso. apply (Hd_min k Hlt). unfold P. split; assumption.
  - exact Hge.
Qed.

(** 部分群の元は g^d の整数冪 *)
Lemma subgroup_element_is_power_of_d :
  forall (C : CyclicGroup) (m : nat) (H : Subgroup C) (d : nat),
    GroupOrder C m ->
    (0 < d)%nat ->
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    (forall k : nat, (0 < k)%nat ->
      subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
      (d <= k)%nat) ->
    forall x : carrier C,
      subgroup_pred C H x ->
      exists n : Z, gpow C (gpow C (generator C) (Z.of_nat d)) n = x.
Proof.
  intros C m H d Hord Hd_pos Hd_in Hd_min x Hx.
  destruct (cyclic_property C x) as [z Hz].
  set (q := z / Z.of_nat d).
  set (r_Z := z mod Z.of_nat d).
  assert (Hdiv : z = Z.of_nat d * q + r_Z).
  { unfold q, r_Z. apply Z.div_mod. lia. }
  assert (Hr_bound : 0 <= r_Z < Z.of_nat d).
  { unfold r_Z. apply Z.mod_pos_bound. lia. }
  assert (Hr_in_H : subgroup_pred C H (gpow C (generator C) r_Z)).
  {
    assert (Heq : gpow C (generator C) r_Z =
                  op C (gpow C (generator C) z)
                        (gpow C (gpow C (generator C) (Z.of_nat d)) (-q))).
    {
      rewrite <- gpow_mul.
      rewrite <- gpow_add.
      f_equal. lia.
    }
    rewrite Heq.
    apply closed_op.
    - rewrite Hz. exact Hx.
    - apply gpow_in_subgroup. exact Hd_in.
  }
  assert (Hr_eq_0 : r_Z = 0).
  {
    destruct (Z.eq_dec r_Z 0) as [H0 | Hne].
    - exact H0.
    - exfalso.
      set (r := Z.to_nat r_Z).
      assert (Hr_pos : (0 < r)%nat).
      { unfold r. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl. lia. }
      assert (Hr_lt_d : (r < d)%nat).
      { unfold r. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
      assert (Hr_in_nat : subgroup_pred C H (gpow C (generator C) (Z.of_nat r))).
      { unfold r. rewrite Z2Nat.id by lia. exact Hr_in_H. }
      assert (Hd_le_r : (d <= r)%nat) by (apply Hd_min; assumption).
      lia.
  }
  exists q.
  rewrite <- gpow_mul.
  rewrite <- Hz.
  f_equal.
  rewrite Hdiv. rewrite Hr_eq_0.
  lia.
Qed.

(** 最小周期は m を割り切る *)
Lemma min_period_divides_group_order :
  forall (C : CyclicGroup) (m : nat) (H : Subgroup C) (d : nat),
    GroupOrder C m ->
    (0 < d)%nat ->
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    (forall k : nat, (0 < k)%nat ->
      subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
      (d <= k)%nat) ->
    Nat.divide d m.
Proof.
  intros C m H d Hord Hd_pos Hd_in Hd_min.
  assert (Hm_pos : (0 < m)%nat) by (apply group_order_pos with (G := C); exact Hord).
  assert (Hm_in : subgroup_pred C H (gpow C (generator C) (Z.of_nat m))).
  { rewrite generator_order by exact Hord. apply contains_e. }
  set (q := (m / d)%nat).
  set (r := (m mod d)%nat).
  assert (Hdivmod : (m = q * d + r)%nat).
  { unfold q, r. pose proof (Nat.div_mod m d ltac:(lia)). lia. }
  assert (Hr_lt : (r < d)%nat).
  { unfold r. apply Nat.mod_upper_bound. lia. }
  assert (Hr_in : subgroup_pred C H (gpow C (generator C) (Z.of_nat r))).
  {
    replace (Z.of_nat r) with (Z.of_nat m - Z.of_nat (q * d)).
    2: { rewrite Nat2Z.inj_mul. lia. }
    replace (Z.of_nat m - Z.of_nat (q * d)) with
            (Z.of_nat m + (- (Z.of_nat d * Z.of_nat q))) by
      (rewrite Nat2Z.inj_mul; ring).
    rewrite gpow_add.
    apply closed_op.
    - exact Hm_in.
    - replace (- (Z.of_nat d * Z.of_nat q)) with (Z.of_nat d * (- Z.of_nat q)) by ring.
      rewrite gpow_mul.
      apply gpow_in_subgroup. exact Hd_in.
  }
  destruct (Nat.eq_dec r 0) as [Hr0 | Hr_ne].
  - subst r. exists q. lia.
  - exfalso.
    assert (Hrpos : (0 < r)%nat) by lia.
    assert (Hd_le_r : (d <= r)%nat) by (apply Hd_min; assumption).
    lia.
Qed.

(** m/d > 0 *)
Lemma m_div_d_pos :
  forall (m d : nat),
    (0 < m)%nat ->
    (0 < d)%nat ->
    Nat.divide d m ->
    (0 < m / d)%nat.
Proof.
  intros m d Hm Hd [q Hq].
  subst m.
  rewrite Nat.div_mul by lia.
  lia.
Qed.

(** Fin変換補題: Fin.to_nat (Fin.of_nat_lt H) = r *)
Lemma to_nat_of_nat_lt : forall (r n : nat) (H : (r < n)%nat),
  proj1_sig (Fin.to_nat (Fin.of_nat_lt H)) = r.
Proof.
  intros r n. revert r. induction n as [|n' IHn]; intros r H.
  - exact (match Nat.nlt_0_r r H with end).
  - destruct r as [|r'].
    + simpl. reflexivity.
    + simpl.
      set (H' := proj2 (Nat.succ_lt_mono r' n') H).
      set (v := Fin.to_nat (Fin.of_nat_lt H')).
      assert (Hrv : proj1_sig v = r') by apply IHn.
      unfold v in *.
      destruct (Fin.to_nat (Fin.of_nat_lt H')) as [i Hi].
      simpl in *. f_equal. exact Hrv.
Qed.

(** g^(d*i) と g^(d*j) は異なる (i < j < m/d のとき) *)
Lemma powers_of_gd_distinct :
  forall (C : CyclicGroup) (m d i j : nat),
    GroupOrder C m ->
    (0 < d)%nat ->
    Nat.divide d m ->
    (i < j)%nat ->
    (j < m / d)%nat ->
    gpow C (generator C) (Z.of_nat (d * i)) <>
    gpow C (generator C) (Z.of_nat (d * j)).
Proof.
  intros C m d i j Hord Hd_pos Hdiv Hij Hj_lt Heq.
  assert (Hperiod : gpow C (generator C) (Z.of_nat (d * j - d * i)) = e C).
  {
    apply equal_powers_imply_period with (i := (d * i)%nat) (j := (d * j)%nat).
    - nia.
    - exact Heq.
  }
  replace (d * j - d * i)%nat with (d * (j - i))%nat in Hperiod by nia.
  assert (Hpos : (0 < d * (j - i))%nat) by nia.
  assert (Hlt_m : (d * (j - i) < m)%nat).
  {
    destruct Hdiv as [q Hq]. subst m.
    rewrite Nat.div_mul in Hj_lt by lia.
    nia.
  }
  assert (Hm_le : (m <= d * (j - i))%nat).
  { apply cyclic_group_order_le_period with (C := C) (m := m) (d := (d * (j - i))%nat).
    exact Hord. exact Hpos. exact Hperiod. }
  lia.
Qed.

(** H の各元は g^(d*r) の形 (r < m/d) *)
Lemma every_subgroup_element_is_small_power :
  forall (C : CyclicGroup) (m d : nat) (H : Subgroup C),
    GroupOrder C m ->
    (0 < d)%nat ->
    Nat.divide d m ->
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    (forall k : nat, (0 < k)%nat ->
      subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
      (d <= k)%nat) ->
    forall x : carrier C,
      subgroup_pred C H x ->
      exists r : nat,
        (r < m / d)%nat /\
        x = gpow C (generator C) (Z.of_nat (d * r)).
Proof.
  intros C m d H Hord Hd_pos Hdiv Hd_in Hd_min x Hx.
  set (md := (m / d)%nat).
  assert (Hmd_pos : (0 < md)%nat).
  { apply m_div_d_pos.
    - apply group_order_pos with (G := C). exact Hord.
    - exact Hd_pos.
    - exact Hdiv. }
  assert (Hmd_eq : (d * md)%nat = m).
  { unfold md. destruct Hdiv as [q Hq]. subst m. rewrite Nat.div_mul by lia. lia. }
  destruct (subgroup_element_is_power_of_d C m H d Hord Hd_pos Hd_in Hd_min x Hx)
    as [n Hn].
  (* (g^d)^n = x, i.e., g^(d*n) = x *)
  assert (Hgdn : gpow C (generator C) (Z.of_nat d * n) = x).
  { rewrite gpow_mul. exact Hn. }
  (* Euclidean division of n by md *)
  set (q_n := n / Z.of_nat md).
  set (r_n := n mod Z.of_nat md).
  assert (Hn_div : n = Z.of_nat md * q_n + r_n).
  { unfold q_n, r_n. apply Z.div_mod. lia. }
  assert (Hr_n_bound : 0 <= r_n < Z.of_nat md).
  { unfold r_n. apply Z.mod_pos_bound. lia. }
  set (r := Z.to_nat r_n).
  exists r.
  split.
  - unfold r, md. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
  - rewrite <- Hgdn.
    assert (Hdr : Z.of_nat (d * r) = Z.of_nat d * r_n).
    { unfold r. rewrite Nat2Z.inj_mul. rewrite Z2Nat.id by lia. ring. }
    rewrite Hdr.
    rewrite Hn_div.
    rewrite Z.mul_add_distr_l.
    rewrite gpow_add.
    assert (Hperiod_part : gpow C (generator C) (Z.of_nat d * (Z.of_nat md * q_n)) = e C).
    {
      replace (Z.of_nat d * (Z.of_nat md * q_n)) with (Z.of_nat (d * md) * q_n).
      2: { rewrite Nat2Z.inj_mul. ring. }
      rewrite Hmd_eq.
      rewrite gpow_mul.
      rewrite generator_order by exact Hord.
      apply gpow_e.
    }
    rewrite Hperiod_part.
    apply id_left.
Qed.

(** 部分群の位数は m/d *)
Lemma subgroup_group_order :
  forall (C : CyclicGroup) (m d : nat) (H : Subgroup C),
    GroupOrder C m ->
    (0 < d)%nat ->
    Nat.divide d m ->
    subgroup_pred C H (gpow C (generator C) (Z.of_nat d)) ->
    (forall k : nat, (0 < k)%nat ->
      subgroup_pred C H (gpow C (generator C) (Z.of_nat k)) ->
      (d <= k)%nat) ->
    GroupOrder (subgroup_group C H) (m / d).
Proof.
  intros C m d H Hord Hd_pos Hdiv Hd_in Hd_min.
  set (md := (m / d)%nat).
  assert (Hmd_pos : (0 < md)%nat).
  { apply m_div_d_pos.
    - apply group_order_pos with (G := C). exact Hord.
    - exact Hd_pos.
    - exact Hdiv. }
  assert (Hmd_eq : (d * md)%nat = m).
  { unfold md. destruct Hdiv as [q Hq]. subst m. rewrite Nat.div_mul by lia. lia. }
  unshelve eexists.
  - intro xH.
    destruct xH as [x Hx].
    destruct (constructive_indefinite_description
      (fun r => (r < md)%nat /\ x = gpow C (generator C) (Z.of_nat (d * r)))
      (every_subgroup_element_is_small_power C m d H Hord Hd_pos Hdiv Hd_in Hd_min x Hx))
      as [r [Hr_lt _]].
    exact (Fin.of_nat_lt Hr_lt).
  - split.
    + (* Injectivity *)
      intros [x1 Hx1] [x2 Hx2] Hfeq.
      apply sig_eq. simpl.
      destruct (constructive_indefinite_description
        (fun r => (r < md)%nat /\ x1 = gpow C (generator C) (Z.of_nat (d * r)))
        (every_subgroup_element_is_small_power C m d H Hord Hd_pos Hdiv Hd_in Hd_min x1 Hx1))
        as [r1 [Hr1_lt Hr1_eq]].
      destruct (constructive_indefinite_description
        (fun r => (r < md)%nat /\ x2 = gpow C (generator C) (Z.of_nat (d * r)))
        (every_subgroup_element_is_small_power C m d H Hord Hd_pos Hdiv Hd_in Hd_min x2 Hx2))
        as [r2 [Hr2_lt Hr2_eq]].
      assert (Hr_eq : r1 = r2).
      {
        assert (H1 : proj1_sig (Fin.to_nat (Fin.of_nat_lt Hr1_lt)) = r1) by apply to_nat_of_nat_lt.
        assert (H2 : proj1_sig (Fin.to_nat (Fin.of_nat_lt Hr2_lt)) = r2) by apply to_nat_of_nat_lt.
        rewrite <- H1, <- H2. f_equal. f_equal. exact Hfeq.
      }
      rewrite Hr1_eq, Hr2_eq, Hr_eq. reflexivity.
    + (* Surjectivity *)
      intro i.
      set (r := proj1_sig (Fin.to_nat i)).
      set (Hr_lt := proj2_sig (Fin.to_nat i)).
      assert (Hdr_in_H : subgroup_pred C H (gpow C (generator C) (Z.of_nat (d * r)))).
      {
        replace (Z.of_nat (d * r)) with (Z.of_nat d * Z.of_nat r) by (rewrite Nat2Z.inj_mul; ring).
        rewrite gpow_mul.
        apply gpow_in_subgroup. exact Hd_in.
      }
      exists (exist _ (gpow C (generator C) (Z.of_nat (d * r))) Hdr_in_H).
      simpl.
      destruct (constructive_indefinite_description
        (fun r' => (r' < md)%nat /\ gpow C (generator C) (Z.of_nat (d * r)) = gpow C (generator C) (Z.of_nat (d * r')))
        (every_subgroup_element_is_small_power C m d H Hord Hd_pos Hdiv Hd_in Hd_min
           (gpow C (generator C) (Z.of_nat (d * r))) Hdr_in_H))
        as [r' [Hr'_lt Hr'_eq]].
      assert (Hr'_eq_r : r' = r).
      {
        destruct (Nat.lt_trichotomy r r') as [Hlt | [Heq | Hgt]].
        - exfalso. apply (powers_of_gd_distinct C m d r r' Hord Hd_pos Hdiv Hlt Hr'_lt).
          exact Hr'_eq.
        - exact (eq_sym Heq).
        - exfalso. apply (powers_of_gd_distinct C m d r' r Hord Hd_pos Hdiv Hgt Hr_lt).
          exact (eq_sym Hr'_eq).
      }
      subst r'.
      apply Fin.to_nat_inj.
      rewrite to_nat_of_nat_lt.
      unfold r.
      reflexivity.
Qed.

(** 巡回群の部分群定理:
    位数 m  の巡回群 C の任意の部分群 H に対して,
      (1) H は巡回群 (ある gen ∈ H が存在し H の全元が gen の冪で表せる),
      (2) H の位数 k は m の約数 (k | m).

    証明の方針:
      C の生成元を g とし,
        S := { n ∈ ℕ | n > 0 ∧ g^n ∈ H }
      とおく.

      [S が非空]
        generator_order より g^m = e ∈ H なので m ∈ S.

      [最小元 d の存在]
        整列原理 (well-ordering principle) により S の最小元 d が存在する.

      [g^d が H を生成する]
        ⊇: gpow_mul と H の部分群性より,
           任意の k ∈ ℤ に対して g^(kd) ∈ H.
        ⊆: x ∈ H とする. C の巡回性より x = g^n となる n ∈ ℤ が存在する.
           Z の除算より n = qd + r (0 ≤ r < d).
           g^r = g^n * (g^d)^{-q} ∈ H (H の部分群性による).
           d の最小性より r = 0 でなければならない.
           よって x = g^(qd) = (g^d)^q.

      [位数 k が m の約数]
        H = ⟨g^d⟩ と g^m = e より d | m.
        |H| = m/d であり, m = (m/d) * d から k | m.              *)

Theorem subgroup_of_cyclic :
  forall (C : CyclicGroup) (m : nat) (H : Subgroup C),
  GroupOrder C m ->
  (* (1) H は巡回群 *)
  (exists gen : carrier C,
     subgroup_pred C H gen /\
     forall x : carrier C,
       subgroup_pred C H x ->
       exists n : Z, gpow C gen n = x) /\
  (* (2) H の位数は m の約数 *)
  (exists k : nat,
     (0 < k)%nat /\
     Nat.divide k m /\
     GroupOrder (subgroup_group C H) k).
Proof.
  intros C m H Hord.
  destruct (min_period_in_subgroup C m H Hord) as [d [Hd_pos [Hd_in Hd_min]]].
  assert (Hdiv : Nat.divide d m).
  { apply min_period_divides_group_order with (H := H); assumption. }
  split.
  - exists (gpow C (generator C) (Z.of_nat d)).
    split.
    + exact Hd_in.
    + intros x Hx.
      apply subgroup_element_is_power_of_d with (m := m) (H := H); assumption.
  - exists (m / d)%nat.
    split.
    + apply m_div_d_pos.
      * apply group_order_pos with (G := C). exact Hord.
      * exact Hd_pos.
      * exact Hdiv.
    + split.
      * destruct Hdiv as [q Hq].
        exists d.
        subst m.
        rewrite Nat.div_mul by lia.
        lia.
      * apply subgroup_group_order with (m := m); assumption.
Qed.

(** 群の直積 (Direct Product of Groups):
    群 G と群 H の直積 G × H を定義する。
    台集合は G の台集合と H の台集合の直積型 (carrier G * carrier H) であり、
    演算・単位元・逆元はそれぞれ成分ごとに定義する:
      - 演算:  (g1, h1) * (g2, h2) := (op G g1 g2, op H h1 h2)
      - 単位元: (e G, e H)
      - 逆元:  (g, h)^{-1} := (inv G g, inv H h)
    各群公理は G と H の対応する公理を成分ごとに適用することで得られる。
    計算透明性を保つため Defined を使用する。  *)
Definition group_product (G H : Group) : Group.
Proof.
  refine {|
    carrier := carrier G * carrier H;
    op      := fun p q => (op G (fst p) (fst q), op H (snd p) (snd q));
    e       := (e G, e H);
    inv     := fun p => (inv G (fst p), inv H (snd p))
  |}.
  - intros [g1 h1] [g2 h2] [g3 h3]. simpl. f_equal; apply assoc.
  - intros [g h]. simpl. f_equal; apply id_left.
  - intros [g h]. simpl. f_equal; apply id_right.
  - intros [g h]. simpl. f_equal; apply inv_left.
  - intros [g h]. simpl. f_equal; apply inv_right.
Defined.

(** 直積群のノーテーション *)
Notation "G ×ₒ H" := (group_product G H) (at level 40, left associativity).

(** ===========================================================
    剰余類群 Z/nZ
    =========================================================== *)

(** 剰余類群 Z/nZ (Residue Class Group Z/nZ):
    n を正の自然数とするとき、整数 Z を n の倍数からなる加法的部分群 nZ で
    割った商群 Z/nZ を定義する。

    台集合として剰余類の代表元の集合 {x : Z | 0 ≤ x < n} を用いる。

      演算 : [a] + [b] := [(a + b) mod n]
      単位元 : [0]
      逆元  : [a]^{-1} := [(-a) mod n]

    証明の方針:
      各群公理を Z の加法と mod の性質から導く。
      - 結合律: Zplus_mod_idemp_l と Zplus_mod_idemp_r を使い、
                両辺を (a + b + c) mod n に変形する。
      - 単位元: Z.mod_small を使い、0 ≤ a < n の代表元は mod で変化しないことを使う。
      - 逆元: Zplus_mod_idemp_l/r と Z.add_opp_diag_l/r から 0 mod n = 0 を導く。  *)

Definition znz_group (n : nat) (Hn : (0 < n)%nat) : Group.
Proof.
  assert (HN : 0 < Z.of_nat n) by lia.
  refine {|
    carrier := { x : Z | 0 <= x < Z.of_nat n };
    op      := fun a b =>
                 exist _ ((proj1_sig a + proj1_sig b) mod Z.of_nat n)
                         (Z.mod_pos_bound _ (Z.of_nat n) HN);
    e       := exist _ 0 (conj (Z.le_refl 0) HN);
    inv     := fun a =>
                 exist _ ((- proj1_sig a) mod Z.of_nat n)
                         (Z.mod_pos_bound _ (Z.of_nat n) HN)
  |}.
  - (* 結合律: ((a + b) mod n + c) mod n = (a + (b + c) mod n) mod n *)
    intros [a Ha] [b Hb] [c Hc]. apply sig_eq. simpl.
    rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Z.add_assoc. reflexivity.
  - (* 左単位元: (0 + a) mod n = a, simpl で 0 + a が a に簡約される *)
    intros [a Ha]. apply sig_eq. simpl.
    apply Z.mod_small. exact Ha.
  - (* 右単位元: (a + 0) mod n = a *)
    intros [a Ha]. apply sig_eq. simpl.
    rewrite Z.add_0_r. apply Z.mod_small. exact Ha.
  - (* 左逆元: ((-a) mod n + a) mod n = 0 *)
    intros [a Ha]. apply sig_eq. simpl.
    rewrite Zplus_mod_idemp_l, Z.add_opp_diag_l. apply Zmod_0_l.
  - (* 右逆元: (a + (-a) mod n) mod n = 0 *)
    intros [a Ha]. apply sig_eq. simpl.
    rewrite Zplus_mod_idemp_r, Z.add_opp_diag_r. apply Zmod_0_l.
Defined.

(** Z/nZ の生成元の自然数冪の値:
    生成元 [1 mod n] を k 回加算すると Z.of_nat k mod n に等しい。

    証明の方針: k に関する帰納法。
      - k = 0: gpow_nat の定義より単位元 [0]。Z.of_nat 0 mod n = 0 mod n = 0。
      - k + 1: 帰納仮定より (1 mod n + Z.of_nat k mod n) mod n を
               Zplus_mod_idemp_l/r を使って (1 + Z.of_nat k) mod n に変形し、
               Nat2Z.inj_succ から Z.of_nat (S k) mod n に等しいことを示す。  *)

Lemma znz_gpow_nat_val : forall (n : nat) (Hn : (0 < n)%nat)
    (Hgen : 0 <= 1 mod Z.of_nat n < Z.of_nat n) (k : nat),
  proj1_sig (gpow_nat (znz_group n Hn)
    (exist _ (1 mod Z.of_nat n) Hgen) k)
  = Z.of_nat k mod Z.of_nat n.
Proof.
  intros n Hn Hgen k.
  induction k as [|k' IH].
  - (* k = 0: gpow_nat gen 0 = e、単位元の値は 0 *)
    simpl. symmetry. apply Zmod_0_l.
  - (* k + 1: Nat2Z.inj_succ を先に適用して Z.of_nat (S k') を展開してから simpl *)
    rewrite Nat2Z.inj_succ.
    simpl. rewrite IH.
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l.
    f_equal. ring.
Qed.

(** Z/nZ は巡回群 (Z/nZ is a Cyclic Group):
    生成元は [1 mod n]:
      - n = 1 のとき: 1 mod 1 = 0 なので生成元は [0]（唯一の元）
      - n ≥ 2 のとき: 生成元は [1]

    任意の元 [x] (0 ≤ x < n) は生成元の x 回の加算として得られる:
      gpow gen (Z.of_nat x) = [x]

    証明の方針:
      [x] に対して k = Z.of_nat (Z.to_nat x) を選び、
      gpow_of_nat と znz_gpow_nat_val を組み合わせて
        proj1_sig (gpow gen k) = Z.of_nat (Z.to_nat x) mod n = x
      を示す。最後に Z.mod_small (0 ≤ x < n) を適用する。  *)

Definition znz_cyclic_group (n : nat) (Hn : (0 < n)%nat) : CyclicGroup.
Proof.
  assert (HN : 0 < Z.of_nat n) by lia.
  assert (Hgen : 0 <= 1 mod Z.of_nat n < Z.of_nat n).
  { apply Z.mod_pos_bound. exact HN. }
  refine {|
    cyclic_group := znz_group n Hn;
    generator    := exist _ (1 mod Z.of_nat n) Hgen
  |}.
  (* 巡回性: 任意の元が生成元の冪として表される *)
  intros [x Hx].
  exists (Z.of_nat (Z.to_nat x)).
  apply sig_eq.
  rewrite gpow_of_nat.
  rewrite znz_gpow_nat_val.
  simpl.
  rewrite Z2Nat.id by lia.
  apply Z.mod_small. exact Hx.
Defined.


(** ===================================================================== *)
(** 既約剰余類群 (Reduced Residue Class Group) (Z/nZ)*                    *)
(** n と互いに素な元 [x] ∈ Z/nZ の全体が乗算 [a]*[b] = [a*b mod n] に    *)
(** 関して群をなす。                                                       *)
(** ===================================================================== *)

(** 補題: Z.gcd 1 n = 1 (1 は任意の n と互いに素)
    証明の方針: Zis_gcd 1 n 1 を直接構成する。
      - 1 | 1, 1 | n は trivial。
      - 任意の公約数 d: d | 1 そのものを返せば よい。  *)
Lemma znz_gcd_one : forall (n : nat),
  Z.gcd 1 (Z.of_nat n) = 1.
Proof.
  intros n.
  apply Zis_gcd_gcd. lia.
  constructor.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros d Hd1 _. exact Hd1.
Qed.

(** 補題: gcd(a mod n, n) = gcd(a, n)  (mod を取っても gcd は不変)
    証明の方針: Z.gcd_mod (Z.gcd a n = Z.gcd n (a mod n)) と
                Z.gcd_comm を組み合わせる。  *)
Lemma znz_gcd_mod_eq : forall (n : nat) (Hn : (0 < n)%nat) (a : Z),
  Z.gcd (a mod Z.of_nat n) (Z.of_nat n) = Z.gcd a (Z.of_nat n).
Proof.
  intros n Hn a.
  (* Z.gcd_mod : Z.gcd (a mod b) b = Z.gcd b a *)
  rewrite Z.gcd_mod by lia.
  apply Z.gcd_comm.
Qed.

(** 補題: gcd(a,n) = 1 かつ gcd(b,n) = 1 ならば gcd(a*b, n) = 1  (乗算の閉包性)
    証明の方針: rel_prime に変換し rel_prime_mult を適用する。  *)
Lemma znz_gcd_mul_coprime : forall (n : nat) (a b : Z),
  Z.gcd a (Z.of_nat n) = 1 ->
  Z.gcd b (Z.of_nat n) = 1 ->
  Z.gcd (a * b) (Z.of_nat n) = 1.
Proof.
  intros n a b Ha Hb.
  assert (Hra : rel_prime (Z.of_nat n) a).
  { unfold rel_prime. apply Zis_gcd_sym. rewrite <- Ha. apply Zgcd_is_gcd. }
  assert (Hrb : rel_prime (Z.of_nat n) b).
  { unfold rel_prime. apply Zis_gcd_sym. rewrite <- Hb. apply Zgcd_is_gcd. }
  assert (Hr : rel_prime (Z.of_nat n) (a * b)).
  { apply rel_prime_mult; assumption. }
  apply Zis_gcd_gcd. lia.
  apply Zis_gcd_sym. exact Hr.
Qed.

(** 補題: gcd(a, n) = 1 ならば乗算逆元が [0, n) に存在し、それも n と互いに素
    証明の方針:
      linear_diophantine で a*u + n*v = 1 となる u, v を取り出し、
      逆元候補を b := u mod n とする。
      1. 0 <= b < n: Z.mod_pos_bound より。
      2. a * b ≡ 1 (mod n): a*(u mod n) ≡ a*u ≡ 1 (mod n) を cong_trans で示す。
      3. gcd(b, n) = 1: d | u かつ d | n ならば d | a*u + n*v = 1 を示す。  *)
Lemma znz_coprime_bezout_inv : forall (n : nat) (Hn : (1 < n)%nat) (a : Z),
  0 <= a < Z.of_nat n ->
  Z.gcd a (Z.of_nat n) = 1 ->
  exists b : Z,
    0 <= b < Z.of_nat n /\
    cong n (a * b) 1 /\
    Z.gcd b (Z.of_nat n) = 1.
Proof.
  intros n Hn a Ha Hgcd.
  assert (HN : 0 < Z.of_nat n) by lia.
  (* linear_diophantine で a*u + n*v = 1 となるベズー係数を取り出す *)
  assert (Hbez : exists u v : Z, a * u + Z.of_nat n * v = 1).
  { apply linear_diophantine. rewrite Hgcd. apply Z.divide_refl. }
  destruct Hbez as [u [v Huv]].
  exists (u mod Z.of_nat n).
  split. { apply Z.mod_pos_bound. lia. }
  split.
  - (* a * (u mod n) ≡ 1 (mod n): a*(u mod n) = a*u - a*(u/n)*n ≡ 1 (mod n) *)
    unfold cong.
    exists (-(v + a * (u / Z.of_nat n))).
    pose proof (Z.div_mod u (Z.of_nat n) ltac:(lia)) as Hdiv.
    (* u mod n = u - n * (u/n) から代入し ring_simplify と lia で示す *)
    assert (Hmod : u mod Z.of_nat n = u - Z.of_nat n * (u / Z.of_nat n)) by lia.
    rewrite Hmod.
    ring_simplify.
    lia.
  - (* gcd(u mod n, n) = 1: u も n と互いに素であることを示す *)
    rewrite znz_gcd_mod_eq by lia.
    (* gcd(u, n) = 1 を Zis_gcd の定義から直接示す *)
    apply Zis_gcd_gcd. lia.
    apply Zis_gcd_sym.
    constructor.
    + apply Z.divide_1_l.
    + apply Z.divide_1_l.
    + (* d | n かつ d | u ならば d | 1: d | a*u + n*v = 1 を利用 *)
      intros d Hdn Hdu.
      assert (Hd_au : (d | a * u)).
      { replace (a * u) with (u * a) by ring. apply Z.divide_mul_l. exact Hdu. }
      assert (Hd_nv : (d | Z.of_nat n * v)).
      { apply Z.divide_mul_l. exact Hdn. }
      assert (Hd1 : (d | a * u + Z.of_nat n * v)).
      { apply Z.divide_add_r; assumption. }
      rewrite Huv in Hd1. exact Hd1.
Qed.

(** 既約剰余類群の逆元の値を epsilon で定義する。
    epsilon は Classical_Epsilon の存在原理を使い、
    性質を満たす b を一意的に取り出す。  *)
Definition znz_units_inv_val (n : nat) (Hn : (1 < n)%nat)
    (a : {x : Z | 0 <= x < Z.of_nat n /\ Z.gcd x (Z.of_nat n) = 1}) : Z :=
  epsilon (inhabits 0%Z)
    (fun b => 0 <= b < Z.of_nat n /\ cong n (proj1_sig a * b) 1 /\ Z.gcd b (Z.of_nat n) = 1).

(** 逆元の性質: znz_units_inv_val は実際に逆元の条件を満たす。
    証明の方針: epsilon_spec に存在証明 znz_coprime_bezout_inv を渡す。  *)
Lemma znz_units_inv_prop : forall (n : nat) (Hn : (1 < n)%nat)
    (a : {x : Z | 0 <= x < Z.of_nat n /\ Z.gcd x (Z.of_nat n) = 1}),
  let b := znz_units_inv_val n Hn a in
  0 <= b < Z.of_nat n /\
  cong n (proj1_sig a * b) 1 /\
  Z.gcd b (Z.of_nat n) = 1.
Proof.
  intros n Hn a.
  unfold znz_units_inv_val.
  apply epsilon_spec.
  exact (znz_coprime_bezout_inv n Hn (proj1_sig a)
           (proj1 (proj2_sig a)) (proj2 (proj2_sig a))).
Qed.

(** 既約剰余類群 (Z/nZ)* の定義
    =====================================================================
    【数学的概要】
    Z/nZ のうち n と互いに素な元 [x]（gcd(x, n) = 1）の全体は、
    剰余乗算 [a] * [b] := [a * b mod n] に関して群をなす。
    これを「既約剰余類群」または「乗法群 (Z/nZ)*」と呼ぶ。

    台集合: {x : Z | 0 <= x < n /\ gcd(x, n) = 1}
    演算:   [a] * [b] := [a * b mod n]
    単位元: [1]
    逆元:   ベズーの補題から存在が保証される乗法逆元

    【Rocq での定義スタイル: Definition ... : Group. Proof. ... Defined.】
    Group レコードには op/e/inv の値フィールドと、
    5つの群公理（結合律・左右単位元・左右逆元）の証明フィールドがある。
    `refine {| ... |}` を使うと、値フィールドをインラインで埋めつつ、
    残った群公理の証明ゴールをタクティクで後から証明できる。
    `Defined`（`Qed` ではなく）で閉じることで計算的透明性を保つ。

    【シグマ型と exist】
    carrier は `{x : Z | P x}` というシグマ型（依存ペア型）である。
    シグマ型の要素を構成するには `exist _ value proof` を使う。
      exist _ v pf : {x : Z | P x}
    これは「値 v と、v が性質 P を満たす証明 pf のペア」を作る。
    op や inv の戻り値もシグマ型なので、必ず exist で包む必要がある。

    【proj1_sig / proj2_sig】
    シグマ型 `{x : T | P x}` から成分を取り出す標準関数:
      proj1_sig : {x : T | P x} -> T          （値の取り出し）
      proj2_sig : forall s : {x : T | P x},   （証明の取り出し）
                  P (proj1_sig s)
    op の定義で `proj1_sig a` と書くのは、シグマ型の要素 a から
    整数値を取り出して乗算するためである。

    【conj / proj1 / proj2】
    carrier の性質は `0 <= x < n /\ gcd(x, n) = 1` という連言 (A /\ B)。
      conj : A -> B -> A /\ B    （連言の構成）
      proj1 : A /\ B -> A        （左成分の取り出し）
      proj2 : A /\ B -> B        （右成分の取り出し）
    exist に渡す証明を `conj pf1 pf2` で組み立て、
    既存の証明から各成分を `proj1 (proj2_sig a)` 等で取り出す。

    【op の証明引数に出てくる補題】
    - Z.mod_pos_bound : 0 < n → 0 <= a mod n < n
        剰余が台集合の範囲条件 (0 <= _ < n) を満たすことを保証する。
    - znz_gcd_mod_eq : gcd(a mod n, n) = gcd(a, n)
        剰余を取っても gcd は変わらないことを示す。
        gcd(a*b mod n, n) = gcd(a*b, n) の変換に使う。
    - znz_gcd_mul_coprime : gcd(a,n)=1 ∧ gcd(b,n)=1 → gcd(a*b,n)=1
        乗算の閉包性。a, b が共に n と互いに素ならば積も互いに素。
    - eq_trans : a = b → b = c → a = c（等号の推移律）
        znz_gcd_mod_eq と znz_gcd_mul_coprime を繋いで
        gcd(a*b mod n, n) = 1 を示す。

    【inv の構成と epsilon】
    逆元の存在は znz_coprime_bezout_inv で「∃ b, ...」として示されるが、
    これは存在命題であり、値そのものではない。
    epsilon (ClassicalEpsilon より) を使うと、
    存在が保証されている値を古典論理によって実際に取り出せる。
      znz_units_inv_val : 逆元の値を epsilon で定義
      znz_units_inv_prop : epsilon_spec を使い逆元の性質を証明

    【群公理証明で使う補題】
    - sig_eq : proj1_sig が等しければシグマ型の等号が成立
        群公理はすべて carrier 上の等号なので、まず sig_eq で
        整数値の等号に帰着させる。
    - Zmult_mod_idemp_l/r : (a mod n) * b mod n = a * b mod n 等
        結合律の証明で、mod を整理するために使う。
    - Z.mul_assoc : a * (b * c) = a * b * c（整数乗算の結合律）
    - Z.mul_1_l/r : 1 * a = a / a * 1 = a（1 が乗算の単位元）
    - Z.mod_small : 0 <= a < n → a mod n = a
        単位元公理で「1 * a mod n = a」を示す際に使う。
    - Z.mod_add : (a + k * n) mod n = a mod n
        逆元公理で「a * b = k * n + 1 → a * b mod n = 1」を示す際に使う。
      *)
Definition znz_units_group (n : nat) (Hn : (1 < n)%nat) : Group.
Proof.
  assert (HN : 0 < Z.of_nat n) by lia.
  assert (Hn_pos : (0 < n)%nat) by lia.
  (* 単位元 1 の carrier 条件を事前に証明:
     H1n は exist で単位元を構成する際の範囲証明として使う *)
  assert (H1n : (0 : Z) <= 1 < Z.of_nat n) by lia.
  (* refine {| ... |}: Group レコードの値フィールドをインラインで埋める。
     残った群公理（結合律・単位元・逆元）の証明ゴールは後続の - ブロックで証明する。 *)
  refine {|
    (* carrier: 台集合。0 <= x < n かつ gcd(x,n) = 1 を満たす整数のシグマ型。 *)
    carrier := {x : Z | 0 <= x < Z.of_nat n /\ Z.gcd x (Z.of_nat n) = 1};

    (* op: 剰余乗算 [a]*[b] = [a*b mod n]。
       戻り値はシグマ型なので exist で包む必要がある。
         - proj1_sig a : シグマ型の要素 a から整数値を取り出す
         - (proj1_sig a * proj1_sig b) mod Z.of_nat n : 乗算して mod を取る
       exist の第3引数（証明）は conj で 2 つの条件を組み立てる:
         条件1（範囲）: Z.mod_pos_bound _ _ HN
                        0 < n ならば 0 <= a*b mod n < n が成立
         条件2（互素）: eq_trans (znz_gcd_mod_eq ...) (znz_gcd_mul_coprime ...)
                        gcd(a*b mod n, n)
                          = gcd(a*b, n)   [znz_gcd_mod_eq: mod と gcd の交換]
                          = 1             [znz_gcd_mul_coprime: 乗算閉包性]
       proj2_sig a の型は (0<=a<n) /\ gcd(a,n)=1 なので、
       proj2 (proj2_sig a) で「gcd(a,n)=1」の部分を取り出している。 *)
    op := fun a b =>
      exist _ ((proj1_sig a * proj1_sig b) mod Z.of_nat n)
        (conj (Z.mod_pos_bound _ _ HN)
              (eq_trans (znz_gcd_mod_eq n Hn_pos (proj1_sig a * proj1_sig b))
                        (znz_gcd_mul_coprime n (proj1_sig a) (proj1_sig b)
                           (proj2 (proj2_sig a)) (proj2 (proj2_sig b)))));

    (* e: 単位元 [1]。
       exist で整数 1 をシグマ型に持ち上げる。
         conj H1n ... : 範囲条件 0 <= 1 < n（H1n は事前に証明済み）
         znz_gcd_one n : gcd(1, n) = 1 *)
    e := exist _ 1 (conj H1n (znz_gcd_one n));

    (* inv: 乗法逆元。
       znz_units_inv_val は epsilon（古典論理）を使って逆元の値を取り出す関数。
       znz_coprime_bezout_inv は「∃ b, 条件」という存在命題を証明するが、
       epsilon を使うことで存在が保証された値を実際に取り出せる。
       exist の証明引数:
         conj (proj1 ...) (proj2 (proj2 ...))
           - proj1 (...): 0 <= b < n（範囲条件）
           - proj2 (proj2 (...)): gcd(b, n) = 1（互素条件）
       znz_units_inv_prop n Hn a の型は
         0 <= b < n /\ cong n (a * b) 1 /\ gcd(b,n) = 1
       なので proj1 で範囲、proj2 (proj2 ...) で互素を取り出す。 *)
    inv := fun a =>
      exist _ (znz_units_inv_val n Hn a)
        (conj (proj1 (znz_units_inv_prop n Hn a))
              (proj2 (proj2 (znz_units_inv_prop n Hn a))))
  |}.
  - (* 結合律: (a*b mod n) * c mod n = a * (b*c mod n) mod n
       sig_eq: proj1_sig が等しければシグマ型の等号が成立するので、
       整数の等号 (a*b mod n) * c mod n = a * (b*c mod n) mod n を証明すればよい。
       Zmult_mod_idemp_r: a * (b mod n) mod n = a * b mod n
       Zmult_mod_idemp_l: (a mod n) * b mod n = a * b mod n
       これらで両辺を a * b * c mod n に変形し、Z.mul_assoc で統一する。 *)
    intros [a Ha] [b Hb] [c Hc]. apply sig_eq. simpl.
    rewrite Zmult_mod_idemp_r, Zmult_mod_idemp_l, Z.mul_assoc. reflexivity.
  - (* 左単位元: 1 * a mod n = a
       sig_eq で整数の等号に帰着。
       Z.mul_1_l: 1 * a = a
       Z.mod_small: 0 <= a < n ならば a mod n = a
       proj1 Ha で範囲条件 0 <= a < n を取り出す。 *)
    intros [a Ha]. apply sig_eq.
    cbn [proj1_sig].
    rewrite Z.mul_1_l. apply Z.mod_small. exact (proj1 Ha).
  - (* 右単位元: a * 1 mod n = a
       Z.mul_1_r: a * 1 = a
       後は左単位元と同様。 *)
    intros [a Ha]. apply sig_eq.
    cbn [proj1_sig].
    rewrite Z.mul_1_r. apply Z.mod_small. exact (proj1 Ha).
  - (* 左逆元: b * a mod n = 1 (b は znz_units_inv_val で取り出した a の逆元)
       sig_eq で整数の等号に帰着。
       znz_units_inv_prop で「cong n (a * b) 1」を取り出す。
         cong n x y の定義: ∃ k, x - y = n * k（n | (x - y)）
       Z.mul_comm で順序を b * a → a * b に変換し、
       cong の定義を展開して a * b = n * k + 1 という形に変形する。
       Z.mod_add: (1 + k * n) mod n = 1 mod n
       Z.mod_small: 0 <= 1 < n ならば 1 mod n = 1 *)
    intros a. apply sig_eq. simpl.
    pose proof (znz_units_inv_prop n Hn a) as Hb.
    destruct Hb as [_ [Hcong _]].
    rewrite Z.mul_comm.
    (* Hcong : cong n (proj1_sig a * znz_units_inv_val n Hn a) 1 *)
    (* = Z.of_nat n | proj1_sig a * b - 1 *)
    (* Goal: proj1_sig a * b mod Z.of_nat n = 1 *)
    unfold cong in Hcong. destruct Hcong as [k Hk].
    assert (Heq : proj1_sig a * znz_units_inv_val n Hn a = Z.of_nat n * k + 1) by lia.
    rewrite Heq.
    replace (Z.of_nat n * k + 1) with (1 + k * Z.of_nat n) by ring.
    rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
  - (* 右逆元: a * b mod n = 1
       左逆元と同様の証明。
       こちらは Z.mul_comm による順序変換が不要（a * b の順番のまま）。 *)
    intros a. apply sig_eq. simpl.
    pose proof (znz_units_inv_prop n Hn a) as Hb.
    destruct Hb as [_ [Hcong _]].
    unfold cong in Hcong. destruct Hcong as [k Hk].
    assert (Heq : proj1_sig a * znz_units_inv_val n Hn a = Z.of_nat n * k + 1) by lia.
    rewrite Heq.
    replace (Z.of_nat n * k + 1) with (1 + k * Z.of_nat n) by ring.
    rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
Defined.

(** ===================================================================== *)
(** 中国剰余定理 (Chinese Remainder Theorem)                               *)
(** 互いに素な p, q と 0<=a<p, 0<=b<q に対して、n mod p = a かつ         *)
(** n mod q = b となる n in [0, p*q) が唯一存在することを示す。           *)
(** ===================================================================== *)

(** 補題: Nat.gcd p q = 1 ならば Bezout 係数が存在する。
    Z.gcd と Nat.gcd の橋渡しを Z.to_nat で行い、
    Nat.gcd_greatest を用いて Z.gcd = 1 を示す。 *)

(** 補助: (Z.of_nat g | Z.of_nat p) ならば Nat.divide g p。 *)
Lemma Z_of_nat_divide_aux : forall (g p : nat),
  (0 < g)%nat -> (Z.of_nat g | Z.of_nat p) -> Nat.divide g p.
Proof.
  intros g p Hg [k Hk].
  assert (Hk_nn : 0 <= k) by (pose proof (Nat2Z.is_nonneg p); nia).
  exists (Z.to_nat k).
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_mul, Z2Nat.id by exact Hk_nn.
  lia.
Qed.

(** 補助: Nat.divide a b ならば (Z.of_nat a | Z.of_nat b)。
    自然数の割り切り関係を整数の割り切り関係に持ち上げる。 *)
Lemma nat_divide_to_Z_of_nat : forall (a b : nat),
  Nat.divide a b -> (Z.of_nat a | Z.of_nat b).
Proof.
  intros a b [k Hk].
  exists (Z.of_nat k).
  rewrite Hk, Nat2Z.inj_mul.
  lia.
Qed.

Lemma nat_coprime_bezout : forall (p q : nat),
  Nat.gcd p q = 1%nat ->
  exists x y : Z, Z.of_nat p * x + Z.of_nat q * y = 1.
Proof.
  intros p q Hgcd.
  assert (HZgcd_div : (Z.gcd (Z.of_nat p) (Z.of_nat q) | 1)).
  {
    pose proof (Z.gcd_divide_l (Z.of_nat p) (Z.of_nat q)) as Hdp.
    pose proof (Z.gcd_divide_r (Z.of_nat p) (Z.of_nat q)) as Hdq.
    pose proof (Z.gcd_nonneg (Z.of_nat p) (Z.of_nat q)) as Hnn.
    set (G := Z.gcd (Z.of_nat p) (Z.of_nat q)) in *.
    set (g := Z.to_nat G).
    assert (HgZ : G = Z.of_nat g).
    { unfold g. rewrite Z2Nat.id; [reflexivity | exact Hnn]. }
    assert (Hgpos : (0 < g)%nat).
    {
      unfold g. apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Hnn. simpl.
      destruct (Z.eq_dec G 0) as [HG0 | HG_ne].
      - exfalso.
        assert (Z.of_nat p = 0) by (apply Z.divide_0_l; rewrite <- HG0; exact Hdp).
        assert (Z.of_nat q = 0) by (apply Z.divide_0_l; rewrite <- HG0; exact Hdq).
        assert (p = 0%nat) by lia. assert (q = 0%nat) by lia. subst.
        simpl in Hgcd. discriminate.
      - lia.
    }
    assert (Hgp : Nat.divide g p).
    { apply Z_of_nat_divide_aux; [exact Hgpos | rewrite <- HgZ; exact Hdp]. }
    assert (Hgq : Nat.divide g q).
    { apply Z_of_nat_divide_aux; [exact Hgpos | rewrite <- HgZ; exact Hdq]. }
    assert (Hg1 : Nat.divide g 1%nat).
    { rewrite <- Hgcd. apply Nat.gcd_greatest; assumption. }
    assert (Hgeq : g = 1%nat) by (apply Nat.divide_1_r; exact Hg1).
    rewrite HgZ, Hgeq. simpl. apply Z.divide_refl.
  }
  apply linear_diophantine. exact HZgcd_div.
Qed.

(** 補題: n mod m = a ならば n ≡ a (mod m)。
    Z.modulo から cong 定義への橋渡し補題。 *)
Lemma cong_of_mod : forall (m : nat) (n a : Z),
  (0 < m)%nat ->
  Z.modulo n (Z.of_nat m) = a ->
  cong m n a.
Proof.
  intros m n a Hm Hmod.
  unfold cong.
  subst a.
  exists (Z.div n (Z.of_nat m)).
  assert (Hm' : Z.of_nat m <> 0) by lia.
  pose proof (Z.div_mod n (Z.of_nat m) Hm') as H.
  lia.
Qed.

(** 補題: 0 <= a < m かつ n ≡ a (mod m) ならば n mod m = a。
    cong 定義から Z.modulo への橋渡し補題。 *)
Lemma mod_of_cong : forall (m : nat) (n a : Z),
  (0 < m)%nat ->
  0 <= a < Z.of_nat m ->
  cong m n a ->
  Z.modulo n (Z.of_nat m) = a.
Proof.
  intros m n a Hm Ha Hcong.
  unfold cong in Hcong.
  destruct Hcong as [k Hk].
  assert (Hn : n = Z.of_nat m * k + a) by lia.
  subst n.
  replace (Z.of_nat m * k + a) with (a + k * Z.of_nat m) by ring.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

(** 補題: 同一範囲に属する合同な整数は等しい。 *)
Lemma cong_unique_in_range : forall (m : nat) (a b : Z),
  (0 < m)%nat ->
  0 <= a < Z.of_nat m ->
  0 <= b < Z.of_nat m ->
  cong m a b ->
  a = b.
Proof.
  intros m a b Hm Ha Hb Hcong.
  unfold cong in Hcong.
  destruct Hcong as [k Hk].
  assert (Hbd : -(Z.of_nat m) < a - b < Z.of_nat m) by lia.
  rewrite Hk in Hbd.
  assert (Hmpos : (0 : Z) < Z.of_nat m) by lia.
  assert (k = 0) by nia.
  lia.
Qed.

(** 補題: 合同関係の推移性。 *)
Lemma cong_trans : forall (m : nat) (a b c : Z),
  cong m a b -> cong m b c -> cong m a c.
Proof.
  intros m a b c H1 H2.
  unfold cong in *.
  replace (a - c) with ((a - b) + (b - c)) by ring.
  apply Z.divide_add_r; assumption.
Qed.

(** 補題: gcd(p,q) = 1 かつ p | a かつ q | a ならば p*q | a。 *)
Lemma coprime_divide_mul : forall (p q : nat) (a : Z),
  Nat.gcd p q = 1%nat ->
  (Z.of_nat p | a) ->
  (Z.of_nat q | a) ->
  (Z.of_nat p * Z.of_nat q | a).
Proof.
  intros p q a Hgcd [i Hi] [j Hj].
  destruct (nat_coprime_bezout p q Hgcd) as [x [y Hxy]].
  exists (i * y + j * x).
  (* p*q*(i*y+j*x) = (p*i)*(q*y) + (q*j)*(p*x) = a*(q*y) + a*(p*x) = a*(p*x+q*y) = a *)
  assert (H1 : Z.of_nat p * i = a). { lia. }
  assert (H2 : Z.of_nat q * j = a). { lia. }
  assert (H3 : Z.of_nat p * Z.of_nat q * (i * y + j * x) =
               (Z.of_nat p * i) * (Z.of_nat q * y) + (Z.of_nat q * j) * (Z.of_nat p * x)).
  { ring. }
  rewrite H1, H2 in H3.
  assert (H4 : a * (Z.of_nat q * y) + a * (Z.of_nat p * x) = a).
  { rewrite <- Z.mul_add_distr_l.
    replace (Z.of_nat q * y + Z.of_nat p * x) with 1.
    - ring.
    - lia. }
  lia.
Qed.

(** 補題: n mod (p*q) は n と mod p および mod q において合同。 *)
Lemma crt_mod_pq : forall (p q : nat) (n : Z),
  (0 < p)%nat ->
  (0 < q)%nat ->
  cong p (Z.modulo n (Z.of_nat p * Z.of_nat q)) n /\
  cong q (Z.modulo n (Z.of_nat p * Z.of_nat q)) n.
Proof.
  intros p q n Hp Hq.
  assert (Hpq : Z.of_nat p * Z.of_nat q <> 0) by lia.
  assert (Hdivmod : n = (Z.of_nat p * Z.of_nat q) *
                    (Z.div n (Z.of_nat p * Z.of_nat q)) +
                    Z.modulo n (Z.of_nat p * Z.of_nat q)).
  { apply Z.div_mod. lia. }
  unfold cong.
  split.
  - exists (-(Z.of_nat q * (Z.div n (Z.of_nat p * Z.of_nat q)))).
    lia.
  - exists (-(Z.of_nat p * (Z.div n (Z.of_nat p * Z.of_nat q)))).
    lia.
Qed.

(** 補題: Bezout 係数から構成した候補解が両方の合同式を満たす。 *)
Lemma crt_solution_cong : forall (p q : nat) (a b x y : Z),
  (0 < p)%nat ->
  (0 < q)%nat ->
  Z.of_nat p * x + Z.of_nat q * y = 1 ->
  let n0 := a * Z.of_nat q * y + b * Z.of_nat p * x in
  cong p n0 a /\ cong q n0 b.
Proof.
  intros p q a b x y Hp Hq Hxy.
  unfold cong.
  split.
  - (* n0 - a = Z.of_nat p * (x*(b-a)) *)
    exists (x * (b - a)).
    assert (Haqy : a * Z.of_nat q * y = a - a * Z.of_nat p * x).
    { assert (Hqy : Z.of_nat q * y = 1 - Z.of_nat p * x). { lia. }
      assert (Hassoc : a * Z.of_nat q * y = a * (Z.of_nat q * y)). { ring. }
      rewrite Hassoc, Hqy. ring. }
    lia.
  - (* n0 - b = Z.of_nat q * (y*(a-b)) *)
    exists (y * (a - b)).
    assert (Hbpx : b * Z.of_nat p * x = b - b * Z.of_nat q * y).
    { assert (Hpx : Z.of_nat p * x = 1 - Z.of_nat q * y). { lia. }
      assert (Hassoc : b * Z.of_nat p * x = b * (Z.of_nat p * x)). { ring. }
      rewrite Hassoc, Hpx. ring. }
    lia.
Qed.

(** 補題: 中国剰余定理の存在性。互いに素な p, q と 0<=a<p, 0<=b<q に対して、
    n mod p = a かつ n mod q = b となる n が [0,p*q) に存在する。 *)
Lemma crt_exists : forall (p q : nat) (a b : Z),
  Nat.gcd p q = 1%nat ->
  (0 < p)%nat ->
  (0 < q)%nat ->
  0 <= a < Z.of_nat p ->
  0 <= b < Z.of_nat q ->
  exists n : Z,
    0 <= n < Z.of_nat p * Z.of_nat q /\
    Z.modulo n (Z.of_nat p) = a /\
    Z.modulo n (Z.of_nat q) = b.
Proof.
  intros p q a b Hgcd Hp Hq Ha Hb.
  (* Bezout 係数を取得: p*x + q*y = 1 *)
  destruct (nat_coprime_bezout p q Hgcd) as [x [y Hxy]].
  (* 候補解を構成 *)
  set (n0 := a * Z.of_nat q * y + b * Z.of_nat p * x).
  set (n := Z.modulo n0 (Z.of_nat p * Z.of_nat q)).
  exists n.
  assert (Hpq_pos : (0 < Z.of_nat p * Z.of_nat q)%Z).
  { lia. }
  (* n \in [0, p*q) *)
  assert (Hbound : 0 <= n < Z.of_nat p * Z.of_nat q).
  { unfold n. apply Z.mod_pos_bound. lia. }
  split. { exact Hbound. }
  (* n0 は cong p n0 a かつ cong q n0 b を満たす *)
  destruct (crt_solution_cong p q a b x y Hp Hq Hxy) as [Hcp Hcq].
  (* n は n0 と mod p および mod q において合同 *)
  destruct (crt_mod_pq p q n0 Hp Hq) as [Hmp Hmq].
  (* cong p n a および cong q n b *)
  assert (Hconp : cong p n a).
  { apply cong_trans with (b := n0). exact Hmp. exact Hcp. }
  assert (Hconq : cong q n b).
  { apply cong_trans with (b := n0). exact Hmq. exact Hcq. }
  split.
  - (* n mod p = a *)
    apply mod_of_cong. exact Hp. split; lia. exact Hconp.
  - (* n mod q = b *)
    apply mod_of_cong. exact Hq. split; lia. exact Hconq.
Qed.

(** 補題: 中国剰余定理の一意性。[0,p*q) の範囲内で条件を満たす解は唯一。 *)
Lemma crt_unique : forall (p q : nat) (n1 n2 : Z),
  Nat.gcd p q = 1%nat ->
  (0 < p)%nat ->
  (0 < q)%nat ->
  0 <= n1 < Z.of_nat p * Z.of_nat q ->
  0 <= n2 < Z.of_nat p * Z.of_nat q ->
  cong p n1 n2 ->
  cong q n1 n2 ->
  n1 = n2.
Proof.
  intros p q n1 n2 Hgcd Hp Hq Hn1 Hn2 Hcp Hcq.
  (* p | (n1 - n2) かつ q | (n1 - n2) なので p*q | (n1 - n2) *)
  assert (Hdivp : (Z.of_nat p | n1 - n2)).
  { exact Hcp. }
  assert (Hdivq : (Z.of_nat q | n1 - n2)).
  { exact Hcq. }
  assert (Hdivpq : (Z.of_nat p * Z.of_nat q | n1 - n2)).
  { apply coprime_divide_mul. exact Hgcd. exact Hdivp. exact Hdivq. }
  (* |n1 - n2| < p*q なので n1 - n2 = 0 *)
  destruct Hdivpq as [k Hk].
  assert (Hrange : -(Z.of_nat p * Z.of_nat q) < n1 - n2 < Z.of_nat p * Z.of_nat q).
  { lia. }
  assert (Hk0 : k = 0).
  { rewrite Hk in Hrange.
    destruct (Z.eq_dec k 0) as [Heq | Hneq].
    - exact Heq.
    - exfalso.
      destruct (Z.lt_ge_cases 0 k) as [Hpos | Hneg].
      + assert (k >= 1) by lia. nia.
      + assert (k <= -1) by lia. nia. }
  subst k. lia.
Qed.

(** 定理: 中国剰余定理 (Chinese Remainder Theorem)。
    p, q を互いに素な自然数、a, b を 0<=a<p, 0<=b<q を満たす整数とすると、
    n mod p = a かつ n mod q = b を満たす n が [0,p*q) に唯一存在する。 *)
Theorem chinese_remainder : forall (p q : nat) (a b : Z),
  Nat.gcd p q = 1%nat ->
  (0 < p)%nat ->
  (0 < q)%nat ->
  0 <= a < Z.of_nat p ->
  0 <= b < Z.of_nat q ->
  exists! n : Z,
    0 <= n < Z.of_nat p * Z.of_nat q /\
    Z.modulo n (Z.of_nat p) = a /\
    Z.modulo n (Z.of_nat q) = b.
Proof.
  intros p q a b Hgcd Hp Hq Ha Hb.
  (* 存在性 *)
  destruct (crt_exists p q a b Hgcd Hp Hq Ha Hb) as [n [Hbound [Hmodp Hmodq]]].
  exists n.
  split.
  - exact (conj Hbound (conj Hmodp Hmodq)).
  - (* 一意性 *)
    intros n' [Hbound' [Hmodp' Hmodq']].
    apply crt_unique with (p := p) (q := q).
    + exact Hgcd.
    + exact Hp.
    + exact Hq.
    + exact Hbound.
    + exact Hbound'.
    + (* cong p n n': n mod p = a = n' mod p *)
      unfold cong.
      assert (Hn := cong_of_mod p n a Hp Hmodp).
      assert (Hn' := cong_of_mod p n' a Hp Hmodp').
      destruct Hn as [k1 Hk1]. destruct Hn' as [k2 Hk2].
      exists (k1 - k2). lia.
    + (* cong q n n' *)
      unfold cong.
      assert (Hn := cong_of_mod q n b Hq Hmodq).
      assert (Hn' := cong_of_mod q n' b Hq Hmodq').
      destruct Hn as [k1 Hk1]. destruct Hn' as [k2 Hk2].
      exists (k1 - k2). lia.
Qed.

(** 3変数版の pairwise coprime 条件。 *)
Definition pairwise_coprime3 (p q r : nat) : Prop :=
  Nat.gcd p q = 1%nat /\ Nat.gcd q r = 1%nat /\ Nat.gcd p r = 1%nat.

(** 補題: pairwise_coprime3 から各 gcd 仮定を取り出す。 *)
Lemma pairwise_coprime3_pq : forall (p q r : nat),
  pairwise_coprime3 p q r -> Nat.gcd p q = 1%nat.
Proof.
  intros p q r [Hpq _]. exact Hpq.
Qed.

Lemma pairwise_coprime3_qr : forall (p q r : nat),
  pairwise_coprime3 p q r -> Nat.gcd q r = 1%nat.
Proof.
  intros p q r [_ [Hqr _]]. exact Hqr.
Qed.

Lemma pairwise_coprime3_pr : forall (p q r : nat),
  pairwise_coprime3 p q r -> Nat.gcd p r = 1%nat.
Proof.
  intros p q r [_ [_ Hpr]]. exact Hpr.
Qed.

(** 補題: pairwise_coprime3 なら gcd(p*q, r) = 1。 *)
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
  { pose proof (Z.gcd_nonneg (Z.of_nat (p * q)) (Z.of_nat r)) as Hnonneg.
    apply Z.divide_1_r_nonneg; [exact Hnonneg | exists k; lia]. }
  apply Nat2Z.inj. simpl.
  apply Z.divide_1_r_nonneg; [apply Nat2Z.is_nonneg | ].
  rewrite <- HgcdZ.
  apply Z.gcd_greatest.
  - apply nat_divide_to_Z_of_nat, Nat.gcd_divide_l.
  - apply nat_divide_to_Z_of_nat, Nat.gcd_divide_r.
Qed.

(** 補題: (mod p*q) の合同は (mod p) に降格できる。 *)
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

(** 補題: (mod p*q) の合同は (mod q) に降格できる。 *)
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

(** 補題: 3つの法で割り切れ、かつ pairwise coprime なら積でも割り切れる。 *)
Lemma coprime_divide_mul_3 : forall (p q r : nat) (a : Z),
  pairwise_coprime3 p q r ->
  (Z.of_nat p | a) ->
  (Z.of_nat q | a) ->
  (Z.of_nat r | a) ->
  (Z.of_nat p * Z.of_nat q * Z.of_nat r | a).
Proof.
  intros p q r a Hpair Hp Hq Hr.
  assert (Hgcd_pq : Nat.gcd p q = 1%nat).
  { apply pairwise_coprime3_pq with (r := r). exact Hpair. }
  assert (Hgcd_pq_r : Nat.gcd (p * q) r = 1%nat).
  { apply pairwise_coprime3_gcd_pq_r. exact Hpair. }
  assert (Hpq_div : (Z.of_nat p * Z.of_nat q | a)).
  { apply coprime_divide_mul; assumption. }
  assert (Hmul : (Z.of_nat (p * q) * Z.of_nat r | a)).
  { apply coprime_divide_mul.
    - exact Hgcd_pq_r.
    - rewrite Nat2Z.inj_mul. exact Hpq_div.
    - exact Hr. }
  rewrite Nat2Z.inj_mul in Hmul.
  exact Hmul.
Qed.

(** 補題: 3変数中国剰余定理の存在性。 *)
Lemma crt_exists_3 : forall (p q r : nat) (a b c : Z),
  pairwise_coprime3 p q r ->
  (0 < p)%nat ->
  (0 < q)%nat ->
  (0 < r)%nat ->
  0 <= a < Z.of_nat p ->
  0 <= b < Z.of_nat q ->
  0 <= c < Z.of_nat r ->
  exists n : Z,
    0 <= n < Z.of_nat p * Z.of_nat q * Z.of_nat r /\
    Z.modulo n (Z.of_nat p) = a /\
    Z.modulo n (Z.of_nat q) = b /\
    Z.modulo n (Z.of_nat r) = c.
Proof.
  intros p q r a b c Hpair Hp Hq Hr Ha Hb Hc.
  assert (Hpq : Nat.gcd p q = 1%nat).
  { apply pairwise_coprime3_pq with (r := r). exact Hpair. }
  assert (Hpq_r : Nat.gcd (p * q) r = 1%nat).
  { apply pairwise_coprime3_gcd_pq_r. exact Hpair. }
  assert (Hpq_pos : (0 < p * q)%nat) by lia.

  destruct (chinese_remainder p q a b Hpq Hp Hq Ha Hb)
    as [t [[Htbound [Htmodp Htmodq]] _]].
  assert (Htbound' : 0 <= t < Z.of_nat (p * q)).
  { rewrite Nat2Z.inj_mul. exact Htbound. }

  destruct (chinese_remainder (p * q) r t c Hpq_r Hpq_pos Hr Htbound' Hc)
    as [n [[Hnbound [Hnmodpq Hnmodr]] _]].

  exists n.
  split.
  - replace (Z.of_nat p * Z.of_nat q * Z.of_nat r)
      with (Z.of_nat (p * q) * Z.of_nat r) by (rewrite Nat2Z.inj_mul; ring).
    exact Hnbound.
  - split.
    + assert (Hcong_n_t_pq : cong (p * q) n t).
      { apply cong_of_mod; [exact Hpq_pos | exact Hnmodpq]. }
      assert (Hcong_n_t_p : cong p n t).
      { apply cong_of_cong_mul_l with (q := q). exact Hcong_n_t_pq. }
      assert (Hcong_t_a_p : cong p t a).
      { apply cong_of_mod; [exact Hp | exact Htmodp]. }
      assert (Hcong_n_a_p : cong p n a).
      { apply cong_trans with (b := t); assumption. }
      apply mod_of_cong; try exact Hp; try exact Ha; exact Hcong_n_a_p.
    + split.
      * assert (Hcong_n_t_pq : cong (p * q) n t).
        { apply cong_of_mod; [exact Hpq_pos | exact Hnmodpq]. }
        assert (Hcong_n_t_q : cong q n t).
        { apply cong_of_cong_mul_r with (p := p). exact Hcong_n_t_pq. }
        assert (Hcong_t_b_q : cong q t b).
        { apply cong_of_mod; [exact Hq | exact Htmodq]. }
        assert (Hcong_n_b_q : cong q n b).
        { apply cong_trans with (b := t); assumption. }
        apply mod_of_cong; try exact Hq; try exact Hb; exact Hcong_n_b_q.
      * exact Hnmodr.
Qed.

(** 補題: 3変数中国剰余定理の一意性。 *)
Lemma crt_unique_3 : forall (p q r : nat) (n1 n2 : Z),
  pairwise_coprime3 p q r ->
  (0 < p)%nat ->
  (0 < q)%nat ->
  (0 < r)%nat ->
  0 <= n1 < Z.of_nat p * Z.of_nat q * Z.of_nat r ->
  0 <= n2 < Z.of_nat p * Z.of_nat q * Z.of_nat r ->
  cong p n1 n2 ->
  cong q n1 n2 ->
  cong r n1 n2 ->
  n1 = n2.
Proof.
  intros p q r n1 n2 Hpair Hp Hq Hr Hn1 Hn2 Hcp Hcq Hcr.
  assert (Hdiv : (Z.of_nat p * Z.of_nat q * Z.of_nat r | n1 - n2)).
  { apply coprime_divide_mul_3; assumption. }
  destruct Hdiv as [k Hk].
  assert (Hrange :
    -(Z.of_nat p * Z.of_nat q * Z.of_nat r) < n1 - n2 < Z.of_nat p * Z.of_nat q * Z.of_nat r).
  { lia. }
  assert (Hk0 : k = 0).
  {
    rewrite Hk in Hrange.
    destruct (Z.eq_dec k 0) as [Heq | Hneq].
    - exact Heq.
    - exfalso.
      destruct (Z.lt_ge_cases 0 k) as [Hpos | Hneg].
      + assert (k >= 1) by lia. nia.
      + assert (k <= -1) by lia. nia.
  }
  subst k. lia.
Qed.

(** 定理: 3変数版中国剰余定理。
    p, q, r が pairwise coprime で、a,b,c が各法の範囲にあるとき、
    3つの合同式を同時に満たす解が [0,p*q*r) に唯一存在する。 *)
Theorem chinese_remainder_3 : forall (p q r : nat) (a b c : Z),
  pairwise_coprime3 p q r ->
  (0 < p)%nat ->
  (0 < q)%nat ->
  (0 < r)%nat ->
  0 <= a < Z.of_nat p ->
  0 <= b < Z.of_nat q ->
  0 <= c < Z.of_nat r ->
  exists! n : Z,
    0 <= n < Z.of_nat p * Z.of_nat q * Z.of_nat r /\
    Z.modulo n (Z.of_nat p) = a /\
    Z.modulo n (Z.of_nat q) = b /\
    Z.modulo n (Z.of_nat r) = c.
Proof.
  intros p q r a b c Hpair Hp Hq Hr Ha Hb Hc.
  destruct (crt_exists_3 p q r a b c Hpair Hp Hq Hr Ha Hb Hc)
    as [n [Hbound [Hmodp [Hmodq Hmodr]]]].
  exists n.
  split.
  - exact (conj Hbound (conj Hmodp (conj Hmodq Hmodr))).
  - intros n' [Hbound' [Hmodp' [Hmodq' Hmodr']]].
    apply crt_unique_3 with (p := p) (q := q) (r := r).
    + exact Hpair.
    + exact Hp.
    + exact Hq.
    + exact Hr.
    + exact Hbound.
    + exact Hbound'.
    + unfold cong.
      assert (Hn := cong_of_mod p n a Hp Hmodp).
      assert (Hn' := cong_of_mod p n' a Hp Hmodp').
      destruct Hn as [k1 Hk1]. destruct Hn' as [k2 Hk2].
      exists (k1 - k2). lia.
    + unfold cong.
      assert (Hn := cong_of_mod q n b Hq Hmodq).
      assert (Hn' := cong_of_mod q n' b Hq Hmodq').
      destruct Hn as [k1 Hk1]. destruct Hn' as [k2 Hk2].
      exists (k1 - k2). lia.
    + unfold cong.
      assert (Hn := cong_of_mod r n c Hr Hmodr).
      assert (Hn' := cong_of_mod r n' c Hr Hmodr').
      destruct Hn as [k1 Hk1]. destruct Hn' as [k2 Hk2].
      exists (k1 - k2). lia.
Qed.

(** ===================================================================== *)
(** Z/nZの分解定理 (Decomposition Theorem for Z/nZ)                       *)
(** p, q, r が pairwise coprime で n = p*q*r のとき、                     *)
(** Z/(pqr)Z ≅ Z/pZ × Z/qZ × Z/rZ を示す。                              *)
(** 写像は φ([a]) = ([a mod p], [a mod q], [a mod r])。                   *)
(** ===================================================================== *)

(** 補助補題: p は p*q*r を割り切る。 *)
Lemma znz_dvd_mul3_l : forall (p q r : nat),
  (Z.of_nat p | Z.of_nat (p * q * r)).
Proof.
  intros p q r.
  rewrite Nat2Z.inj_mul, Nat2Z.inj_mul.
  exists (Z.of_nat q * Z.of_nat r).
  ring.
Qed.

(** 補助補題: q は p*q*r を割り切る。 *)
Lemma znz_dvd_mul3_m : forall (p q r : nat),
  (Z.of_nat q | Z.of_nat (p * q * r)).
Proof.
  intros p q r.
  rewrite Nat2Z.inj_mul, Nat2Z.inj_mul.
  exists (Z.of_nat p * Z.of_nat r).
  ring.
Qed.

(** 補助補題: r は p*q*r を割り切る。 *)
Lemma znz_dvd_mul3_r : forall (p q r : nat),
  (Z.of_nat r | Z.of_nat (p * q * r)).
Proof.
  intros p q r.
  rewrite Nat2Z.inj_mul, Nat2Z.inj_mul.
  exists (Z.of_nat p * Z.of_nat q).
  ring.
Qed.

(** 補助補題: (a mod (p*q*r)) mod p = a mod p。
    mod_mod_divide (stdlib) と znz_dvd_mul3_l から直接得られる。 *)
Lemma znz_mod_mod_l : forall (p q r : nat) (a : Z),
  (0 < p)%nat ->
  (a mod Z.of_nat (p * q * r)) mod Z.of_nat p = a mod Z.of_nat p.
Proof.
  intros p q r a Hp.
  apply Z.mod_mod_divide.
  apply znz_dvd_mul3_l.
Qed.

(** 補助補題: (a mod (p*q*r)) mod q = a mod q。 *)
Lemma znz_mod_mod_m : forall (p q r : nat) (a : Z),
  (0 < q)%nat ->
  (a mod Z.of_nat (p * q * r)) mod Z.of_nat q = a mod Z.of_nat q.
Proof.
  intros p q r a Hq.
  apply Z.mod_mod_divide.
  apply znz_dvd_mul3_m.
Qed.

(** 補助補題: (a mod (p*q*r)) mod r = a mod r。 *)
Lemma znz_mod_mod_r : forall (p q r : nat) (a : Z),
  (0 < r)%nat ->
  (a mod Z.of_nat (p * q * r)) mod Z.of_nat r = a mod Z.of_nat r.
Proof.
  intros p q r a Hr.
  apply Z.mod_mod_divide.
  apply znz_dvd_mul3_r.
Qed.

(** Z/nZの分解定理:
    p, q, r が pairwise coprime のとき、
    Z/(pqr)Z ≅ Z/pZ × Z/qZ × Z/rZ。

    写像: φ([a]) = (([a mod p], [a mod q]), [a mod r])

    証明の方針:
    - 準同型性: mod_mod_divide + Zplus_mod を用いて各成分の等号を示す。
    - 単射性: crt_unique_3 から a = b (Z 値として) を導き sig_eq で等号を得る。
    - 全射性: crt_exists_3 で任意の (x,y,z) の逆像を構成する。  *)

Theorem znz_decomp :
  forall (p q r : nat) (Hp : (0 < p)%nat) (Hq : (0 < q)%nat) (Hr : (0 < r)%nat)
    (Hpqr : (0 < p * q * r)%nat),
    pairwise_coprime3 p q r ->
    znz_group (p * q * r) Hpqr ≅
    znz_group p Hp ×ₒ znz_group q Hq ×ₒ znz_group r Hr.
Proof.
  intros p q r Hp Hq Hr Hpqr Hpair.
  assert (HN : 0 < Z.of_nat (p * q * r)) by lia.
  assert (HP : 0 < Z.of_nat p) by lia.
  assert (HQ : 0 < Z.of_nat q) by lia.
  assert (HR : 0 < Z.of_nat r) by lia.
  (* 写像 φ の定義 *)
  set (phi := fun (a : carrier (znz_group (p * q * r) Hpqr)) =>
    ( ( exist (fun x => 0 <= x < Z.of_nat p)
              (proj1_sig a mod Z.of_nat p)
              (Z.mod_pos_bound (proj1_sig a) (Z.of_nat p) HP)
      , exist (fun x => 0 <= x < Z.of_nat q)
              (proj1_sig a mod Z.of_nat q)
              (Z.mod_pos_bound (proj1_sig a) (Z.of_nat q) HQ)
      )
    , exist (fun x => 0 <= x < Z.of_nat r)
              (proj1_sig a mod Z.of_nat r)
              (Z.mod_pos_bound (proj1_sig a) (Z.of_nat r) HR)
    ) : carrier (znz_group p Hp ×ₒ znz_group q Hq ×ₒ znz_group r Hr)).
  exists phi.
  unfold IsIsomorphism. split; [| split].

  (* ====== 準同型性 ====== *)
  - intros [a Ha] [b Hb].
    unfold phi. simpl.
    (* 各成分について (a + b) mod (pqr) mod p = ((a mod p) + (b mod p)) mod p を示す *)
    assert (Hmod_l : (a + b) mod Z.of_nat (p * q * r) mod Z.of_nat p =
                     (a mod Z.of_nat p + b mod Z.of_nat p) mod Z.of_nat p).
    { rewrite znz_mod_mod_l by exact Hp.
      rewrite <- Zplus_mod. reflexivity. }
    assert (Hmod_m : (a + b) mod Z.of_nat (p * q * r) mod Z.of_nat q =
                     (a mod Z.of_nat q + b mod Z.of_nat q) mod Z.of_nat q).
    { rewrite znz_mod_mod_m by exact Hq.
      rewrite <- Zplus_mod. reflexivity. }
    assert (Hmod_r : (a + b) mod Z.of_nat (p * q * r) mod Z.of_nat r =
                     (a mod Z.of_nat r + b mod Z.of_nat r) mod Z.of_nat r).
    { rewrite znz_mod_mod_r by exact Hr.
      rewrite <- Zplus_mod. reflexivity. }
    f_equal.
    + f_equal.
      * apply sig_eq. simpl. exact Hmod_l.
      * apply sig_eq. simpl. exact Hmod_m.
    + apply sig_eq. simpl. exact Hmod_r.

  (* ====== 単射性 ====== *)
  - intros [a Ha] [b Hb] Heq.
    apply sig_eq. simpl.
    (* injection Heq が直接 a mod p = b mod p などの値の等号を生成する *)
    unfold phi in Heq. simpl in Heq.
    injection Heq as H1 H2 H3.
    (* Z.of_nat (p*q*r) = Z.of_nat p * Z.of_nat q * Z.of_nat r に変換 *)
    assert (Hmul : Z.of_nat (p * q * r) = Z.of_nat p * Z.of_nat q * Z.of_nat r).
    { rewrite !Nat2Z.inj_mul. ring. }
    assert (Ha' : 0 <= a < Z.of_nat p * Z.of_nat q * Z.of_nat r).
    { rewrite <- Hmul. exact Ha. }
    assert (Hb' : 0 <= b < Z.of_nat p * Z.of_nat q * Z.of_nat r).
    { rewrite <- Hmul. exact Hb. }
    (* crt_unique_3 を適用: cong p a b, cong q a b, cong r a b から a = b *)
    apply crt_unique_3 with (p := p) (q := q) (r := r).
    + exact Hpair.
    + exact Hp.
    + exact Hq.
    + exact Hr.
    + exact Ha'.
    + exact Hb'.
    + (* cong p a b: a mod p = b mod p → p | a - b *)
      unfold cong. apply Z.mod_divide.
      * lia.
      * rewrite Zminus_mod, H1, Z.sub_diag. apply Zmod_0_l.
    + unfold cong. apply Z.mod_divide.
      * lia.
      * rewrite Zminus_mod, H2, Z.sub_diag. apply Zmod_0_l.
    + unfold cong. apply Z.mod_divide.
      * lia.
      * rewrite Zminus_mod, H3, Z.sub_diag. apply Zmod_0_l.

  (* ====== 全射性 ====== *)
  - intros [[[x Hx] [y Hy]] [z Hz]].
    (* crt_exists_3 で逆像を構成 *)
    destruct (crt_exists_3 p q r x y z Hpair Hp Hq Hr Hx Hy Hz)
      as [n [Hn [Hnp [Hnq Hnr]]]].
    assert (Hn_bound : 0 <= n < Z.of_nat (p * q * r)).
    { rewrite Nat2Z.inj_mul, Nat2Z.inj_mul. exact Hn. }
    exists (exist _ n Hn_bound).
    unfold phi. simpl.
    f_equal.
    + f_equal.
      * apply sig_eq. simpl. exact Hnp.
      * apply sig_eq. simpl. exact Hnq.
    + apply sig_eq. simpl. exact Hnr.
Qed.

(** ===================================================================== *)
(** 既約剰余類群の分解定理                                                *)
(** Decomposition Theorem for the Group of Units (Z/nZ)^*                 *)
(** p, q, r が pairwise coprime で n = p*q*r のとき、                     *)
(** (Z/(pqr)Z)^* ≅ (Z/pZ)^* × (Z/qZ)^* × (Z/rZ)^* を示す。             *)
(** 写像は φ([a]) = ([a mod p], [a mod q], [a mod r])。                   *)
(** ===================================================================== *)

(** 補助補題: gcd(a, m*n) = 1 ならば gcd(a, m) = 1。
    d が a と m の公約数であれば、m | m*n より d | m*n となり、
    d | gcd(a, m*n) = 1 が成り立つ。Zis_gcd の第3フィールドを利用。 *)
Lemma znz_units_gcd_dvd : forall (m n : nat) (a : Z),
  Z.gcd a (Z.of_nat (m * n)) = 1 ->
  Z.gcd a (Z.of_nat m) = 1.
Proof.
  intros m n a H.
  apply Zis_gcd_gcd. lia.
  constructor.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros d Hda Hdm.
    assert (Hmn : Zis_gcd a (Z.of_nat (m * n)) 1).
    { rewrite <- H. apply Zgcd_is_gcd. }
    destruct Hmn as [_ _ H3].
    apply H3.
    + exact Hda.
    + rewrite Nat2Z.inj_mul. apply Z.divide_mul_l. exact Hdm.
Qed.

(** 補助補題: gcd(a, m) = 1 かつ gcd(a, n) = 1 ならば gcd(a, m*n) = 1。
    rel_prime_mult を利用: rel_prime a m かつ rel_prime a n → rel_prime a (m*n)。 *)
Lemma znz_units_gcd_mul : forall (m n : nat) (a : Z),
  Z.gcd a (Z.of_nat m) = 1 ->
  Z.gcd a (Z.of_nat n) = 1 ->
  Z.gcd a (Z.of_nat (m * n)) = 1.
Proof.
  intros m n a Hm Hn.
  assert (Hrm : rel_prime a (Z.of_nat m)).
  { unfold rel_prime. rewrite <- Hm. apply Zgcd_is_gcd. }
  assert (Hrn : rel_prime a (Z.of_nat n)).
  { unfold rel_prime. rewrite <- Hn. apply Zgcd_is_gcd. }
  assert (Hr : rel_prime a (Z.of_nat m * Z.of_nat n)).
  { apply rel_prime_mult; assumption. }
  rewrite Nat2Z.inj_mul.
  apply Zis_gcd_gcd. lia.
  exact Hr.
Qed.

(** 補助補題: gcd(a, p*q*r) = 1 ならば gcd(a mod p, p) = 1。
    znz_units_gcd_dvd で gcd(a, p) = 1 を得て、znz_gcd_mod_eq で mod に変換する。
    p*q*r = p * (q*r) に変形して znz_units_gcd_dvd を適用する。 *)
Lemma znz_units_coprime_mod_l : forall (p q r : nat) (Hp : (0 < p)%nat) (a : Z),
  Z.gcd a (Z.of_nat (p * q * r)) = 1 ->
  Z.gcd (a mod Z.of_nat p) (Z.of_nat p) = 1.
Proof.
  intros p q r Hp a H.
  rewrite znz_gcd_mod_eq by exact Hp.
  apply (znz_units_gcd_dvd p (q * r)).
  rewrite Nat.mul_assoc. exact H.
Qed.

(** 補助補題: gcd(a, p*q*r) = 1 ならば gcd(a mod q, q) = 1。 *)
Lemma znz_units_coprime_mod_m : forall (p q r : nat) (Hq : (0 < q)%nat) (a : Z),
  Z.gcd a (Z.of_nat (p * q * r)) = 1 ->
  Z.gcd (a mod Z.of_nat q) (Z.of_nat q) = 1.
Proof.
  intros p q r Hq a H.
  rewrite znz_gcd_mod_eq by exact Hq.
  apply (znz_units_gcd_dvd q (p * r)).
  rewrite Nat.mul_assoc. rewrite (Nat.mul_comm q p). exact H.
Qed.

(** 補助補題: gcd(a, p*q*r) = 1 ならば gcd(a mod r, r) = 1。 *)
Lemma znz_units_coprime_mod_r : forall (p q r : nat) (Hr : (0 < r)%nat) (a : Z),
  Z.gcd a (Z.of_nat (p * q * r)) = 1 ->
  Z.gcd (a mod Z.of_nat r) (Z.of_nat r) = 1.
Proof.
  intros p q r Hr a H.
  rewrite znz_gcd_mod_eq by exact Hr.
  apply (znz_units_gcd_dvd r (p * q)).
  rewrite (Nat.mul_comm r (p * q)). exact H.
Qed.

(** 補助補題: gcd(a,p)=1 ∧ gcd(a,q)=1 ∧ gcd(a,r)=1 ならば gcd(a, p*q*r) = 1。
    znz_units_gcd_mul を2回適用する。 *)
Lemma znz_units_gcd_mul3 : forall (p q r : nat) (a : Z),
  Z.gcd a (Z.of_nat p) = 1 ->
  Z.gcd a (Z.of_nat q) = 1 ->
  Z.gcd a (Z.of_nat r) = 1 ->
  Z.gcd a (Z.of_nat (p * q * r)) = 1.
Proof.
  intros p q r a Hp Hq Hr.
  apply (znz_units_gcd_mul (p * q) r).
  - apply (znz_units_gcd_mul p q); assumption.
  - exact Hr.
Qed.

(** 補助補題: (a * b) mod (p*q*r) mod p = (a mod p * (b mod p)) mod p。
    znz_mod_mod_l で mod (p*q*r) mod p = mod p に簡約し、
    Z.mul_mod で乗算の mod 分配則を適用する。 *)
Lemma znz_units_decomp_mul_mod : forall (p q r : nat) (Hp : (0 < p)%nat) (a b : Z),
  (a * b) mod Z.of_nat (p * q * r) mod Z.of_nat p =
  (a mod Z.of_nat p * (b mod Z.of_nat p)) mod Z.of_nat p.
Proof.
  intros p q r Hp a b.
  rewrite znz_mod_mod_l by exact Hp.
  apply Z.mul_mod. lia.
Qed.

(** 既約剰余類群の分解定理:
    p, q, r が pairwise coprime のとき、
    (Z/(pqr)Z)^* ≅ (Z/pZ)^* × (Z/qZ)^* × (Z/rZ)^*。

    写像: φ([a]) = (([a mod p], [a mod q]), [a mod r])

    証明の方針:
    - 写像の定義: 各成分の range と gcd=1 を znz_units_coprime_mod_l/m/r で示す。
    - 準同型性: znz_units_decomp_mul_mod で乗算の mod 分配則を適用。
    - 単射性: crt_unique_3 から a = b を導き sig_eq で等号を得る。
    - 全射性: crt_exists_3 で逆像を構成し、znz_units_gcd_mul3 で gcd 条件を示す。 *)

Theorem znz_units_decomp :
  forall (p q r : nat) (Hp : (1 < p)%nat) (Hq : (1 < q)%nat) (Hr : (1 < r)%nat)
    (Hpqr : (1 < p * q * r)%nat),
    pairwise_coprime3 p q r ->
    znz_units_group (p * q * r) Hpqr ≅
    znz_units_group p Hp ×ₒ znz_units_group q Hq ×ₒ znz_units_group r Hr.
Proof.
  intros p q r Hp Hq Hr Hpqr Hpair.
  assert (HP : (0 < p)%nat) by lia.
  assert (HQ : (0 < q)%nat) by lia.
  assert (HR : (0 < r)%nat) by lia.
  assert (HPQR : (0 < p * q * r)%nat) by lia.
  assert (HP' : 0 < Z.of_nat p) by lia.
  assert (HQ' : 0 < Z.of_nat q) by lia.
  assert (HR' : 0 < Z.of_nat r) by lia.
  (* 写像 φ の定義 *)
  set (phi := fun (a : carrier (znz_units_group (p * q * r) Hpqr)) =>
    ( ( exist (fun x => 0 <= x < Z.of_nat p /\ Z.gcd x (Z.of_nat p) = 1)
              (proj1_sig a mod Z.of_nat p)
              (conj (Z.mod_pos_bound (proj1_sig a) (Z.of_nat p) HP')
                    (znz_units_coprime_mod_l p q r HP (proj1_sig a)
                       (proj2 (proj2_sig a))))
      , exist (fun x => 0 <= x < Z.of_nat q /\ Z.gcd x (Z.of_nat q) = 1)
              (proj1_sig a mod Z.of_nat q)
              (conj (Z.mod_pos_bound (proj1_sig a) (Z.of_nat q) HQ')
                    (znz_units_coprime_mod_m p q r HQ (proj1_sig a)
                       (proj2 (proj2_sig a))))
      )
    , exist (fun x => 0 <= x < Z.of_nat r /\ Z.gcd x (Z.of_nat r) = 1)
              (proj1_sig a mod Z.of_nat r)
              (conj (Z.mod_pos_bound (proj1_sig a) (Z.of_nat r) HR')
                    (znz_units_coprime_mod_r p q r HR (proj1_sig a)
                       (proj2 (proj2_sig a))))
    ) : carrier (znz_units_group p Hp ×ₒ znz_units_group q Hq ×ₒ znz_units_group r Hr)).
  exists phi.
  unfold IsIsomorphism. split; [| split].

  (* ====== 準同型性 ====== *)
  - intros [a Ha] [b Hb].
    unfold phi. simpl.
    f_equal.
    + f_equal.
      * apply sig_eq. simpl.
        rewrite znz_mod_mod_l by exact HP. apply Z.mul_mod. lia.
      * apply sig_eq. simpl.
        rewrite znz_mod_mod_m by exact HQ. apply Z.mul_mod. lia.
    + apply sig_eq. simpl.
      rewrite znz_mod_mod_r by exact HR. apply Z.mul_mod. lia.

  (* ====== 単射性 ====== *)
  - intros [a Ha] [b Hb] Heq.
    apply sig_eq. simpl.
    unfold phi in Heq. simpl in Heq.
    injection Heq as H1 H2 H3.
    assert (Hmul : Z.of_nat (p * q * r) = Z.of_nat p * Z.of_nat q * Z.of_nat r).
    { rewrite !Nat2Z.inj_mul. ring. }
    assert (Ha' : 0 <= a < Z.of_nat p * Z.of_nat q * Z.of_nat r).
    { rewrite <- Hmul. exact (proj1 Ha). }
    assert (Hb' : 0 <= b < Z.of_nat p * Z.of_nat q * Z.of_nat r).
    { rewrite <- Hmul. exact (proj1 Hb). }
    apply crt_unique_3 with (p := p) (q := q) (r := r).
    + exact Hpair.
    + exact HP.
    + exact HQ.
    + exact HR.
    + exact Ha'.
    + exact Hb'.
    + unfold cong. apply Z.mod_divide. lia.
      rewrite Zminus_mod, H1, Z.sub_diag. apply Zmod_0_l.
    + unfold cong. apply Z.mod_divide. lia.
      rewrite Zminus_mod, H2, Z.sub_diag. apply Zmod_0_l.
    + unfold cong. apply Z.mod_divide. lia.
      rewrite Zminus_mod, H3, Z.sub_diag. apply Zmod_0_l.

  (* ====== 全射性 ====== *)
  - intros [[[x Hx] [y Hy]] [z Hz]].
    destruct (crt_exists_3 p q r x y z Hpair HP HQ HR (proj1 Hx) (proj1 Hy) (proj1 Hz))
      as [n [Hn [Hnp [Hnq Hnr]]]].
    assert (Hn_range : 0 <= n < Z.of_nat (p * q * r)).
    { rewrite Nat2Z.inj_mul, Nat2Z.inj_mul. exact Hn. }
    (* gcd(n, p*q*r) = 1 を構成する *)
    assert (Hgp : Z.gcd n (Z.of_nat p) = 1).
    { rewrite <- znz_gcd_mod_eq by exact HP.
      rewrite Hnp. exact (proj2 Hx). }
    assert (Hgq : Z.gcd n (Z.of_nat q) = 1).
    { rewrite <- znz_gcd_mod_eq by exact HQ.
      rewrite Hnq. exact (proj2 Hy). }
    assert (Hgr : Z.gcd n (Z.of_nat r) = 1).
    { rewrite <- znz_gcd_mod_eq by exact HR.
      rewrite Hnr. exact (proj2 Hz). }
    assert (Hgpqr : Z.gcd n (Z.of_nat (p * q * r)) = 1).
    { apply znz_units_gcd_mul3; assumption. }
    exists (exist _ n (conj Hn_range Hgpqr)).
    unfold phi. simpl.
    f_equal.
    + f_equal.
      * apply sig_eq. simpl. exact Hnp.
      * apply sig_eq. simpl. exact Hnq.
    + apply sig_eq. simpl. exact Hnr.
Qed.

(** ===========================================================
    オイラー関数 (Euler's Totient Function)
    =========================================================== *)

(** オイラー関数 (Euler's Totient Function):

    euler_phi n と定義する。

    この値は乗法群 (Z/nZ)^* の位数と一致する。

    定義: euler_phi n = |{k ∈ {0,...,n-1} | gcd(k, n) = 1}|  *)

Require Import Stdlib.Lists.List.
Import ListNotations.

Definition euler_phi (n : nat) : nat :=
  List.length (List.filter
    (fun k => Z.eqb (Z.gcd (Z.of_nat k) (Z.of_nat n)) 1)
    (List.seq 0 n)).

(** GroupOrder の一意性:
    群 G の位数が m かつ n であれば m = n。
    証明の方針:
      GroupOrder G m より全単射 f : G → Fin.t m が存在する。
      GroupOrder G n より全単射 g : G → Fin.t n が存在する。
      f の逆関数を使って Fin.t n → G → Fin.t m の単射を構成し、
      Fin_injective_le で n ≤ m、逆方向でも m ≤ n を得る。  *)

Lemma group_order_unique : forall (G : Group) (m n : nat),
  GroupOrder G m -> GroupOrder G n -> m = n.
Proof.
  intros G m n [f [Hfinj Hfsurj]] [g [Hginj Hgsurj]].
  (* epsilon で右逆写像を構成する *)
  set (xf := fun (i : Fin.t m) =>
    epsilon (inhabits (e G)) (fun x => f x = i)).
  assert (Hxf : forall i : Fin.t m, f (xf i) = i).
  { intro i. apply epsilon_spec. exact (Hfsurj i). }
  set (xg := fun (i : Fin.t n) =>
    epsilon (inhabits (e G)) (fun x => g x = i)).
  assert (Hxg : forall i : Fin.t n, g (xg i) = i).
  { intro i. apply epsilon_spec. exact (Hgsurj i). }
  apply Nat.le_antisymm.
  - (* m ≤ n: φ := i ↦ g(xf(i)) は Fin.t m → Fin.t n の単射 *)
    apply Fin_injective_le with (phi := fun i => g (xf i)).
    intros i j Heq.
    assert (Hxeq : xf i = xf j) by (apply Hginj; exact Heq).
    assert (Hfeq : f (xf i) = f (xf j)) by (apply f_equal; exact Hxeq).
    rewrite (Hxf i), (Hxf j) in Hfeq. exact Hfeq.
  - (* n ≤ m: φ := i ↦ f(xg(i)) は Fin.t n → Fin.t m の単射 *)
    apply Fin_injective_le with (phi := fun i => f (xg i)).
    intros i j Heq.
    assert (Hxeq : xg i = xg j) by (apply Hfinj; exact Heq).
    assert (Hgeq : g (xg i) = g (xg j)) by (apply f_equal; exact Hxeq).
    rewrite (Hxg i), (Hxg j) in Hgeq. exact Hgeq.
Qed.

(** GroupOrder の同型不変性:
    G ≅ H かつ GroupOrder G m ならば GroupOrder H m。
    証明の方針:
      G ≅ H より同型写像 φ : G → H が存在する (全単射)。
      GroupOrder G m より全単射 f : G → Fin.t m が存在する。
      合成 f ∘ φ^{-1} : H → Fin.t m が全単射になる。
      実装: φ の全射性から写像 ψ : H → G (φ(ψ(h)) = h) を構成し、
      f ∘ ψ を全単射とする。  *)

Lemma group_order_iso : forall (G H : Group) (m : nat),
  G ≅ H -> GroupOrder G m -> GroupOrder H m.
Proof.
  intros G H m [phi [Hhom [Hinj Hsurj]]] [f [Hfinj Hfsurj]].
  (* epsilon で φ の右逆 ψ を構成する: φ(ψ(h)) = h *)
  set (psi := fun (h : carrier H) =>
    epsilon (inhabits (e G)) (fun x => phi x = h)).
  assert (Hphi_psi : forall h, phi (psi h) = h).
  { intro h. apply epsilon_spec. exact (Hsurj h). }
  assert (Hpsi_phi : forall x, psi (phi x) = x).
  { intro x. apply Hinj. exact (Hphi_psi (phi x)). }
  (* f ∘ ψ : H → Fin.t m *)
  exists (fun h => f (psi h)).
  split.
  - (* 単射性: f(ψ(h1)) = f(ψ(h2)) → h1 = h2 *)
    intros h1 h2 Heq.
    assert (Hpsi : psi h1 = psi h2) by (apply Hfinj; exact Heq).
    assert (Hph : phi (psi h1) = phi (psi h2)) by (apply f_equal; exact Hpsi).
    rewrite (Hphi_psi h1), (Hphi_psi h2) in Hph. exact Hph.
  - (* 全射性: 任意の i : Fin.t m に対し φ(x) を返す *)
    intro i.
    destruct (Hfsurj i) as [x Hx].
    exists (phi x).
    rewrite Hpsi_phi. exact Hx.
Qed.

(** 直積群の位数:
    GroupOrder G m かつ GroupOrder H n ならば GroupOrder (G ×ₒ H) (m * n)。
    証明の方針:
      f : G → Fin.t m, g : H → Fin.t n の全単射から
      (x, y) ↦ Fin.of_nat_lt (i * n + j < m * n) を構成する。
      ただし i = proj1_sig (Fin.to_nat (f x)), j = proj1_sig (Fin.to_nat (g y))。
      単射性: i1*n+j1 = i2*n+j2 かつ 0 ≤ j < n から i1 = i2, j1 = j2。
      全射性: Fin.t (m*n) の任意の k から商 k/n と余り k mod n を取り出す。  *)

Lemma product_index_lt : forall (i j m n : nat),
  (i < m)%nat -> (j < n)%nat -> (i * n + j < m * n)%nat.
Proof. intros. nia. Qed.

Lemma product_index_unique : forall (i1 j1 i2 j2 n : nat),
  (j1 < n)%nat -> (j2 < n)%nat ->
  (i1 * n + j1 = i2 * n + j2)%nat ->
  i1 = i2 /\ j1 = j2.
Proof.
  intros i1 j1 i2 j2 n Hj1 Hj2 Heq.
  assert (Hi : i1 = i2).
  { destruct (Nat.lt_trichotomy i1 i2) as [H|[H|H]].
    - exfalso. nia.
    - exact H.
    - exfalso. nia. }
  split. exact Hi. lia.
Qed.

Lemma group_order_product : forall (G H : Group) (m n : nat),
  GroupOrder G m -> GroupOrder H n ->
  GroupOrder (G ×ₒ H) (m * n).
Proof.
  intros G H m n [f [Hfinj Hfsurj]] [g [Hginj Hgsurj]].
  (* 写像の定義: (x, y) ↦ Fin.of_nat_lt で i*n+j をエンコード
     ただし i = proj1_sig (Fin.to_nat (f x)), j = proj1_sig (Fin.to_nat (g y)) *)
  set (h := fun (p : carrier G * carrier H) =>
    let i  := proj1_sig (Fin.to_nat (f (fst p))) in
    let j  := proj1_sig (Fin.to_nat (g (snd p))) in
    let Hi := proj2_sig (Fin.to_nat (f (fst p))) in
    let Hj := proj2_sig (Fin.to_nat (g (snd p))) in
    Fin.of_nat_lt (product_index_lt i j m n Hi Hj)).
  exists h.
  split.
  - (* 単射性: h (x1,y1) = h (x2,y2) → (x1,y1) = (x2,y2) *)
    intros [x1 y1] [x2 y2] Heq.
    unfold h in Heq. simpl in Heq.
    pose proof (f_equal (fun x => proj1_sig (Fin.to_nat x)) Heq) as Hval.
    cbv beta in Hval.
    set (i1 := proj1_sig (Fin.to_nat (f x1))).
    set (j1 := proj1_sig (Fin.to_nat (g y1))).
    set (i2 := proj1_sig (Fin.to_nat (f x2))).
    set (j2 := proj1_sig (Fin.to_nat (g y2))).
    set (Hi1 := proj2_sig (Fin.to_nat (f x1))).
    set (Hj1 := proj2_sig (Fin.to_nat (g y1))).
    set (Hi2 := proj2_sig (Fin.to_nat (f x2))).
    set (Hj2 := proj2_sig (Fin.to_nat (g y2))).
    assert (A1 : proj1_sig (Fin.to_nat
      (Fin.of_nat_lt (product_index_lt i1 j1 m n Hi1 Hj1))) = (i1*n+j1)%nat)
      by apply to_nat_of_nat_lt.
    assert (A2 : proj1_sig (Fin.to_nat
      (Fin.of_nat_lt (product_index_lt i2 j2 m n Hi2 Hj2))) = (i2*n+j2)%nat)
      by apply to_nat_of_nat_lt.
    assert (Hval2 : (i1*n+j1 = i2*n+j2)%nat).
    { exact (eq_trans (eq_sym A1) (eq_trans Hval A2)). }
    destruct (product_index_unique i1 j1 i2 j2 n Hj1 Hj2 Hval2) as [Hi_eq Hj_eq].
    simpl. f_equal.
    + apply Hfinj. apply Fin.to_nat_inj. exact Hi_eq.
    + apply Hginj. apply Fin.to_nat_inj. exact Hj_eq.
  - (* 全射性: 任意の k : Fin.t (m*n) に対し (x,y) を構成する *)
    intro k.
    set (kv := proj1_sig (Fin.to_nat k)).
    assert (Hk : (kv < m * n)%nat) by exact (proj2_sig (Fin.to_nat k)).
    assert (Hn_pos : (0 < n)%nat).
    { destruct n as [| n'].
      - simpl in Hk. lia.
      - lia. }
    set (i := (kv / n)%nat).
    set (j := (kv mod n)%nat).
    assert (Hi_lt : (i < m)%nat).
    { unfold i. apply Nat.div_lt_upper_bound. lia. lia. }
    assert (Hj_lt : (j < n)%nat) by (unfold j; apply Nat.mod_upper_bound; lia).
    destruct (Hfsurj (Fin.of_nat_lt Hi_lt)) as [x Hx].
    destruct (Hgsurj (Fin.of_nat_lt Hj_lt)) as [y Hy].
    exists (x, y).
    unfold h. simpl.
    apply Fin.to_nat_inj.
    rewrite to_nat_of_nat_lt.
    (* proj1_sig (to_nat (f x)) = i、proj1_sig (to_nat (g y)) = j を示す *)
    assert (Hfx : proj1_sig (Fin.to_nat (f x)) = i).
    { rewrite Hx. apply to_nat_of_nat_lt. }
    assert (Hgy : proj1_sig (Fin.to_nat (g y)) = j).
    { rewrite Hy. apply to_nat_of_nat_lt. }
    rewrite Hfx, Hgy.
    unfold i, j, kv.
    rewrite Nat.mul_comm. symmetry. apply Nat.div_mod. lia.
Qed.

(** euler_phi と znz_units_group の位数の接続:
    n > 1 のとき GroupOrder (znz_units_group n Hn) (euler_phi n) が成立する。

    証明の方針:
      L := filter (fun k => gcd(k,n) = 1) (seq 0 n) とすると euler_phi n = |L| 。
      キャリア x = (z, proof) に対し k := Z.to_nat z は L にEcho
      epsilon で k の L 内インデックス pos を取り出し、
      f x := Fin.of_nat_lt (pos < |L|) を全単射として示す。
        単射性: NoDup L から異なる k  pos を持つ。は異な
        全射性: 各 i に対し L の i 番目の要素から carrier 要素を構成する。  *)

Lemma filter_seq_NoDup : forall (n : nat) (p : nat -> bool),
  List.NoDup (List.filter p (List.seq 0 n)).
Proof.
  intros n p.
  apply List.NoDup_filter.
  apply List.seq_NoDup.
Qed.

Lemma filter_seq_elem_bound : forall (n k : nat) (p : nat -> bool),
  List.In k (List.filter p (List.seq 0 n)) -> (k < n)%nat.
Proof.
  intros n k p Hk.
  apply List.filter_In in Hk.
  destruct Hk as [Hseq _].
  apply List.in_seq in Hseq. lia.
Qed.

Lemma euler_phi_group_order : forall (n : nat) (Hn : (1 < n)%nat),
  GroupOrder (znz_units_group n Hn) (euler_phi n).
Proof.
  intros n Hn.
  set (L := List.filter
    (fun k => Z.eqb (Z.gcd (Z.of_nat k) (Z.of_nat n)) 1)
    (List.seq 0 n)).
  assert (HL_nd : List.NoDup L) by (apply filter_seq_NoDup).
  (* キャリア要素の nat 表現が L に属することを示す *)
  assert (Hcarrier_in_L : forall (x : carrier (znz_units_group n Hn)),
    List.In (Z.to_nat (proj1_sig x)) L).
  { intro x.
    destruct x as [z [[Hlo Hhi] Hgcd]]. simpl.
    apply List.filter_In.
    split.
    - apply List.in_seq. simpl.
      split. { lia. }
      apply (Nat2Z.inj_lt (Z.to_nat z) n).
      rewrite Z2Nat.id by lia. exact Hhi.
    - apply Z.eqb_eq.
      rewrite Z2Nat.id by lia.
      exact Hgcd. }
  (* epsilon でインデックスを取り出す関数を定義 *)
  set (pos := fun (x : carrier (znz_units_group n Hn)) =>
    epsilon (inhabits 0%nat)
      (fun p => (p < List.length L)%nat /\
                List.nth p L 0%nat = Z.to_nat (proj1_sig x))).
  assert (Hpos_spec : forall x : carrier (znz_units_group n Hn),
    (pos x < List.length L)%nat /\
    List.nth (pos x) L 0%nat = Z.to_nat (proj1_sig x)).
  { intro x.
    apply epsilon_spec.
    destruct (List.In_nth L (Z.to_nat (proj1_sig x)) 0%nat
                (Hcarrier_in_L x)) as [p [Hp_lt Hp_eq]].
    exact (ex_intro _ p (conj Hp_lt Hp_eq)). }
  (* f x := Fin.of_nat_lt (pos x < |L|) を全単射として示す *)
  exists (fun x => Fin.of_nat_lt (proj1 (Hpos_spec x))).
  split.
  - (* 単射性: f x = f y → x = y *)
    intros x y Heq.
    apply sig_eq. simpl.
    pose proof (f_equal (fun i => proj1_sig (Fin.to_nat i)) Heq) as Hval.
    cbv beta in Hval.
    rewrite !to_nat_of_nat_lt in Hval.
    (* Hval : pos x = pos y *)
    destruct (Hpos_spec x) as [Hpos_lt_x Hx].
    destruct (Hpos_spec y) as [Hpos_lt_y Hy].
    assert (Hk : Z.to_nat (proj1_sig x) = Z.to_nat (proj1_sig y)).
    { rewrite <- Hx, <- Hy, Hval. reflexivity. }
    assert (Hrange_x : 0 <= proj1_sig x) by (exact (proj1 (proj1 (proj2_sig x)))).
    assert (Hrange_y : 0 <= proj1_sig y) by (exact (proj1 (proj1 (proj2_sig y)))).
    apply Z2Nat.inj. exact Hrange_x. exact Hrange_y. exact Hk.
  - (* 全射性: 各 i に対し carrier 要素を構成する *)
    intro i.
    set (p := proj1_sig (Fin.to_nat i)).
    assert (Hp_lt : (p < List.length L)%nat) by exact (proj2_sig (Fin.to_nat i)).
    set (k := List.nth p L 0%nat).
    assert (Hk_in_L : List.In k L).
    { unfold k. apply List.nth_In. exact Hp_lt. }
    apply List.filter_In in Hk_in_L.
    destruct Hk_in_L as [Hk_seq Hk_eqb].
    apply List.in_seq in Hk_seq.
    apply Z.eqb_eq in Hk_eqb.
    assert (Hk_lt : (k < n)%nat) by lia.
    assert (Hk_range : 0 <= Z.of_nat k < Z.of_nat n).
    { split. lia. apply Nat2Z.inj_lt. exact Hk_lt. }
    (* carrier 要素 x0 = exist (Z.of_nat k) (...) を構成する *)
    set (x0cond := conj Hk_range Hk_eqb
      : 0 <= Z.of_nat k < Z.of_nat n /\ Z.gcd (Z.of_nat k) (Z.of_nat n) = 1).
    exists (exist _ (Z.of_nat k) x0cond : carrier (znz_units_group n Hn)).
    (* f x0 = i を示す *)
    simpl.
    apply Fin.to_nat_inj.
    rewrite to_nat_of_nat_lt.
    (* pos x0 = p = proj1_sig (Fin.to_nat i) を示す *)
    destruct (Hpos_spec (exist _ (Z.of_nat k) x0cond))
      as [Hpos_lt Hpos_eq].
    simpl in Hpos_eq.
    rewrite Nat2Z.id in Hpos_eq.
    (* Hpos_eq : List.nth (pos x0) L 0 = k *)
    (* p = proj1_sig (Fin.to_nat i) *)
    (* Show: pos x0 = p using NoDup *)
    apply (proj1 (List.NoDup_nth L 0%nat) HL_nd (pos _) p Hpos_lt Hp_lt).
    rewrite Hpos_eq. unfold k. reflexivity.
Qed.

(** 補助補題 (2変数版): gcd(a, p*q) = 1 ならば gcd(a mod p, p) = 1。 *)
Lemma znz_units_coprime_mod2_l : forall (p q : nat) (Hp : (0 < p)%nat) (a : Z),
  Z.gcd a (Z.of_nat (p * q)) = 1 ->
  Z.gcd (a mod Z.of_nat p) (Z.of_nat p) = 1.
Proof.
  intros p q Hp a H.
  rewrite znz_gcd_mod_eq by exact Hp.
  apply (znz_units_gcd_dvd p q). exact H.
Qed.

(** 補助補題 (2変数版): gcd(a, p*q) = 1 ならば gcd(a mod q, q) = 1。 *)
Lemma znz_units_coprime_mod2_m : forall (p q : nat) (Hq : (0 < q)%nat) (a : Z),
  Z.gcd a (Z.of_nat (p * q)) = 1 ->
  Z.gcd (a mod Z.of_nat q) (Z.of_nat q) = 1.
Proof.
  intros p q Hq a H.
  rewrite znz_gcd_mod_eq by exact Hq.
  apply (znz_units_gcd_dvd q p).
  rewrite Nat.mul_comm. exact H.
Qed.

(** 補助補題 (2変数版): (a mod (p*q)) mod p = a mod p。 *)
Lemma znz_mod_mod2_l : forall (p q : nat) (a : Z),
  (0 < p)%nat ->
  (a mod Z.of_nat (p * q)) mod Z.of_nat p = a mod Z.of_nat p.
Proof.
  intros p q a Hp.
  apply Z.mod_mod_divide.
  rewrite Nat2Z.inj_mul.
  exists (Z.of_nat q). ring.
Qed.

(** 補助補題 (2変数版): (a mod (p*q)) mod q = a mod q。 *)
Lemma znz_mod_mod2_m : forall (p q : nat) (a : Z),
  (0 < q)%nat ->
  (a mod Z.of_nat (p * q)) mod Z.of_nat q = a mod Z.of_nat q.
Proof.
  intros p q a Hq.
  apply Z.mod_mod_divide.
  rewrite Nat2Z.inj_mul.
  exists (Z.of_nat p). ring.
Qed.

(** 2変数版の既約剰余類群分解定理:
    p, q が互いに素のとき、(Z/(pq)Z)^* ≅ (Z/pZ)^* × (Z/qZ)^*。

    写像: φ([a]) = ([a mod p], [a mod q])

    証明の方針:
    - 写像の定義: znz_units_coprime_mod2_l/m で gcd 条件を示す。
    - 準同型性: znz_mod_mod2_l/m + Z.mul_mod で乗算の mod 分配則を適用。
    - 単射: crt_unique で a = b を導き sig_eq で等号を得る。
    - 全射性: crt_exists で逆像を構成し、znz_units_gcd_mul で gcd 条件を示す。 *)
Lemma znz_units_decomp2 :
  forall (p q : nat) (Hp : (1 < p)%nat) (Hq : (1 < q)%nat)
    (Hpq : (1 < p * q)%nat),
    Nat.gcd p q = 1%nat ->
    znz_units_group (p * q) Hpq ≅ znz_units_group p Hp ×ₒ znz_units_group q Hq.
Proof.
  intros p q Hp Hq Hpq Hgcd.
  assert (HP : (0 < p)%nat) by lia.
  assert (HQ : (0 < q)%nat) by lia.
  assert (HP' : 0 < Z.of_nat p) by lia.
  assert (HQ' : 0 < Z.of_nat q) by lia.
  (* 写像 φ の定義 *)
  set (phi := fun (a : carrier (znz_units_group (p * q) Hpq)) =>
    ( exist (fun x => 0 <= x < Z.of_nat p /\ Z.gcd x (Z.of_nat p) = 1)
            (proj1_sig a mod Z.of_nat p)
            (conj (Z.mod_pos_bound (proj1_sig a) (Z.of_nat p) HP')
                  (znz_units_coprime_mod2_l p q HP (proj1_sig a)
                     (proj2 (proj2_sig a))))
    , exist (fun x => 0 <= x < Z.of_nat q /\ Z.gcd x (Z.of_nat q) = 1)
            (proj1_sig a mod Z.of_nat q)
            (conj (Z.mod_pos_bound (proj1_sig a) (Z.of_nat q) HQ')
                  (znz_units_coprime_mod2_m p q HQ (proj1_sig a)
                     (proj2 (proj2_sig a))))
    ) : carrier (znz_units_group p Hp ×ₒ znz_units_group q Hq)).
  exists phi.
  unfold IsIsomorphism. split; [| split].

  (* ====== 準同型性 ====== *)
  - intros [a Ha] [b Hb].
    unfold phi. simpl.
    f_equal.
    + apply sig_eq. simpl.
      rewrite znz_mod_mod2_l by exact HP. apply Z.mul_mod. lia.
    + apply sig_eq. simpl.
      rewrite znz_mod_mod2_m by exact HQ. apply Z.mul_mod. lia.

  (* ====== 単射性 ====== *)
  - intros [a Ha] [b Hb] Heq.
    apply sig_eq. simpl.
    unfold phi in Heq. simpl in Heq.
    injection Heq as H1 H2.
    assert (Hmul : Z.of_nat (p * q) = Z.of_nat p * Z.of_nat q).
    { rewrite Nat2Z.inj_mul. ring. }
    assert (Ha' : 0 <= a < Z.of_nat p * Z.of_nat q).
    { rewrite <- Hmul. exact (proj1 Ha). }
    assert (Hb' : 0 <= b < Z.of_nat p * Z.of_nat q).
    { rewrite <- Hmul. exact (proj1 Hb). }
    apply crt_unique with (p := p) (q := q).
    + exact Hgcd.
    + exact HP.
    + exact HQ.
    + exact Ha'.
    + exact Hb'.
    + unfold cong. apply Z.mod_divide. lia.
      rewrite Zminus_mod, H1, Z.sub_diag. apply Zmod_0_l.
    + unfold cong. apply Z.mod_divide. lia.
      rewrite Zminus_mod, H2, Z.sub_diag. apply Zmod_0_l.

  (* ====== 全射性 ====== *)
  - intros [[x Hx] [y Hy]].
    destruct (crt_exists p q x y Hgcd HP HQ (proj1 Hx) (proj1 Hy))
      as [n [Hn [Hnp Hnq]]].
    assert (Hn_range : 0 <= n < Z.of_nat (p * q)).
    { rewrite Nat2Z.inj_mul. exact Hn. }
    assert (Hgp : Z.gcd n (Z.of_nat p) = 1).
    { rewrite <- znz_gcd_mod_eq by exact HP.
      rewrite Hnp. exact (proj2 Hx). }
    assert (Hgq : Z.gcd n (Z.of_nat q) = 1).
    { rewrite <- znz_gcd_mod_eq by exact HQ.
      rewrite Hnq. exact (proj2 Hy). }
    assert (Hgpq : Z.gcd n (Z.of_nat (p * q)) = 1).
    { apply znz_units_gcd_mul; assumption. }
    exists (exist _ n (conj Hn_range Hgpq)).
    unfold phi. simpl.
    f_equal.
    + apply sig_eq. simpl. exact Hnp.
    + apply sig_eq. simpl. exact Hnq.
Qed.

(** オイラー関数の乗法性:
    p, q が互いに素のとき phi(p*q) = phi(p) * phi(q)。

    証明の方針:
    1. znz_units_decomp2 で (Z/pqZ)^* ≅ (Z/pZ)^* ×ₒ (Z/qZ)^*
    2. euler_phi_group_order で GroupOrder (units (Z/pqZ)) (euler_phi (p*q)) など
    3. group_order_iso + group_order_product で等式を得る
    4. group_order_unique で一意性から phi(p*q) = phi(p) * phi(q) *)
Lemma euler_phi_mul :
  forall (p q : nat) (Hp : (1 < p)%nat) (Hq : (1 < q)%nat),
    Nat.gcd p q = 1%nat ->
    euler_phi (p * q) = (euler_phi p * euler_phi q)%nat.
Proof.
  intros p q Hp Hq Hgcd.
  assert (Hpq : (1 < p * q)%nat) by nia.
  (* GroupOrder (units pqZ) (euler_phi (p*q)) *)
  assert (Hord_pq : GroupOrder (znz_units_group (p * q) Hpq) (euler_phi (p * q))).
  { apply euler_phi_group_order. }
  (* GroupOrder (units pZ) (euler_phi p) *)
  assert (Hord_p : GroupOrder (znz_units_group p Hp) (euler_phi p)).
  { apply euler_phi_group_order. }
  (* GroupOrder (units qZ) (euler_phi q) *)
  assert (Hord_q : GroupOrder (znz_units_group q Hq) (euler_phi q)).
  { apply euler_phi_group_order. }
  (* GroupOrder (units pZ ×ₒ units qZ) (euler_phi p * euler_phi q) *)
  assert (Hord_prod : GroupOrder (znz_units_group p Hp ×ₒ znz_units_group q Hq)
                                  (euler_phi p * euler_phi q)).
  { apply group_order_product; assumption. }
  (* units pqZ ≅ units pZ ×ₒ units qZ *)
  assert (Hiso : znz_units_group (p * q) Hpq ≅
                   znz_units_group p Hp ×ₒ znz_units_group q Hq).
  { apply znz_units_decomp2; assumption. }
  (* GroupOrder (units pZ ×ₒ units qZ) (euler_phi (p*q)):
     group_order_iso の方向は G ≅ H → GroupOrder G m → GroupOrder H m なので
     Hiso (units pqZ ≅ units pZ × units qZ) と Hord_pq を使う *)
  assert (Hord_prod2 : GroupOrder (znz_units_group p Hp ×ₒ znz_units_group q Hq)
                                   (euler_phi (p * q))).
  { apply (group_order_iso (znz_units_group (p * q) Hpq)); assumption. }
  (* 一意性で等式を得る *)
  apply (group_order_unique (znz_units_group p Hp ×ₒ znz_units_group q Hq)); assumption.
Qed.

(** 補助補題: 素数 p のとき gcd(k, p^e) = 1 ↔ p ∤ k。
    前向き: p|k なら p | gcd(k, p^e) | 1 となり矛盾 (prime_ge_2)。
    後向き: ¬(p|k) なら prime_rel_prime で rel_prime p k を得て、
            coprime_pow_r で rel_prime k (p^e) を導く。 *)
Lemma prime_pow_coprime_iff :
  forall (p e k : nat),
    prime (Z.of_nat p) ->
    (1 <= e)%nat ->
    (Z.gcd (Z.of_nat k) (Z.of_nat (p ^ e)) = 1 <->
     (k mod p <> 0)%nat).
Proof.
  intros p e k Hprime He.
  assert (Hp2 : (2 <= Z.of_nat p)) by (apply prime_ge_2; exact Hprime).
  assert (Hp_pos : (0 < p)%nat) by lia.
  rewrite Nat2Z.inj_pow.
  split.
  - (* 前向き: gcd = 1 → p ∤ k *)
    intros Hgcd Hmod.
    (* k mod p = 0 → p | k *)
    assert (Hpk : (Z.of_nat p | Z.of_nat k)).
    { apply Z.mod_divide. lia.
      rewrite <- Nat2Z.inj_mod, Hmod. simpl. reflexivity. }
    (* p | p^e (e ≥ 1 なので) *)
    assert (Hppe : (Z.of_nat p | Z.of_nat p ^ Z.of_nat e)).
    { replace (Z.of_nat p ^ Z.of_nat e)
        with (Z.of_nat p * Z.of_nat p ^ (Z.of_nat e - 1)).
      - apply Z.divide_factor_l.
      - rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
    (* p | gcd(k, p^e) *)
    assert (Hpdvd : (Z.of_nat p | Z.gcd (Z.of_nat k) (Z.of_nat p ^ Z.of_nat e))).
    { apply Z.gcd_greatest. exact Hpk. exact Hppe. }
    (* gcd(k, p^e) = 1 と矛盾: p | 1 かつ p ≥ 2 *)
    rewrite Hgcd in Hpdvd.
    assert (Hle : Z.of_nat p <= 1) by (apply Z.divide_pos_le; [lia | exact Hpdvd]).
    lia.
  - (* 後向き: p ∤ k → gcd = 1 *)
    intros Hmod.
    (* k mod p ≠ 0 → ¬(p | k) in Z *)
    assert (Hpk : ~ (Z.of_nat p | Z.of_nat k)).
    { intro Hdvd.
      apply Hmod.
      apply Nat2Z.inj.
      rewrite Nat2Z.inj_mod.
      apply Z.mod_divide in Hdvd; [| lia].
      rewrite Hdvd. simpl. reflexivity. }
    (* prime_rel_prime: ¬(p|k) → rel_prime p k *)
    assert (Hrel : rel_prime (Z.of_nat p) (Z.of_nat k)).
    { apply prime_rel_prime; assumption. }
    (* rel_prime p k → rel_prime k p → rel_prime k (p^e) *)
    assert (Hrel2 : rel_prime (Z.of_nat k) (Z.of_nat p)).
    { apply rel_prime_sym. exact Hrel. }
    (* Z.gcd k p = 1 → Z.gcd k (p^e) = 1 using coprime_pow_r *)
    unfold rel_prime in Hrel2.
    assert (Hgcd_one : Z.gcd (Z.of_nat k) (Z.of_nat p) = 1).
    { apply Zis_gcd_gcd. lia. exact Hrel2. }
    (* coprime k p → coprime k (p^e) *)
    apply Z.coprime_pow_r. lia. exact Hgcd_one.
Qed.

(** 補助補題: (p * m + r) mod p = r (0 < p, r < p のとき)。
    mod_add の性質を使って直接示す。 *)
Lemma mod_add_mul_small : forall p r m : nat,
  (0 < p)%nat -> (r < p)%nat -> ((p * m + r) mod p = r)%nat.
Proof.
  intros p r m Hp Hr.
  rewrite Nat.mul_comm, Nat.add_comm. rewrite Nat.Div0.mod_add.
  apply Nat.mod_small. exact Hr.
Qed.

(** 補助補題: すべての要素で述語が偽なら filter は空リストを返す。 *)
Lemma filter_false_forall :
  forall (A : Type) (f : A -> bool) (l : list A),
    List.Forall (fun x => f x = false) l ->
    List.filter f l = [].
Proof.
  intros A f l H. induction H as [| x xs Hx Hxs IH].
  - reflexivity.
  - cbn [List.filter]. rewrite Hx. exact IH.
Qed.

(** 補助補題: seq (p*m) p をフィルタすると [p*m] のみが残る。
    つまり区間 [p*m, p*m+p) 中の p の倍数は p*m (1つだけ) である。 *)
Lemma filter_window_single_multiple :
  forall (p m : nat),
    (0 < p)%nat ->
    List.filter (fun k => Nat.eqb (Nat.modulo k p) 0) (List.seq (p * m) p) = [(p * m)%nat].
Proof.
  intros p m Hp.
  destruct p as [| p']. { lia. }
  (* seq (S p' * m) (S p') = (S p' * m) :: seq (S(S p' * m)) p' *)
  cbn [List.seq].
  (* filter の先頭要素を取り出す *)
  cbn [List.filter].
  assert (Hhead : Nat.eqb ((S p' * m) mod (S p')) 0 = true).
  { apply Nat.eqb_eq. rewrite Nat.mul_comm. apply Nat.Div0.mod_mul. }
  rewrite Hhead.
  (* 残要素のフィルタ: S(S p' * m) から p' 個の中に S p' の倍数はない *)
  assert (Htail : List.filter (fun k => Nat.eqb (Nat.modulo k (S p')) 0)
                    (List.seq (S (S p' * m)) p') = []).
  { apply filter_false_forall.
    apply List.Forall_forall. intros k Hk_in.
    apply List.in_seq in Hk_in. destruct Hk_in as [Hlo Hhi].
    apply Nat.eqb_neq.
    assert (Hr1 : (1 <= k - S p' * m)%nat) by lia.
    assert (Hr2 : (k - S p' * m <= p')%nat) by lia.
    assert (Hk_eq : (k = S p' * m + (k - S p' * m))%nat) by lia.
    rewrite Hk_eq. rewrite mod_add_mul_small; lia. }
  rewrite Htail. reflexivity.
Qed.

(** 補助補題: [0, p*m) 中の p の倍数の個数は m である。
    証明は帰納法: seq 0 (p*(m+1)) = seq 0 (p*m) ++ seq (p*m) p の分割を使い、
    後者の中に p の倍数は p*m (1つだけ) があることを示す。 *)
Lemma count_multiples_in_range :
  forall (p m : nat),
    (0 < p)%nat ->
    List.length (List.filter (fun k => Nat.eqb (k mod p) 0) (List.seq 0 (p * m))) = m.
Proof.
  intros p m Hp.
  induction m as [| m' IHm'].
  - rewrite Nat.mul_0_r. reflexivity.
  - replace (p * S m')%nat with (p * m' + p)%nat by lia.
    rewrite (List.seq_app (p * m') p 0).
    rewrite List.filter_app, List.app_length, IHm'.
    replace (0 + p * m')%nat with (p * m')%nat by lia.
    rewrite filter_window_single_multiple. 2: exact Hp.
    simpl. lia.
Qed.

(** 素数冪のオイラー関数:
    prime p かつ 1 ≤ e のとき phi(p^e) = p^(e-1) * (p-1)。

    証明の方針:
    1. euler_phi (p^e) = |{k < p^e | gcd(k,p^e)=1}|
    2. prime_pow_coprime_iff: gcd(k,p^e)=1 ↔ k mod p ≠ 0
    3. 補数: |{k | gcd=1}| = p^e - |{k | p|k}| = p^e - p^(e-1)
    4. 等式: p^e - p^(e-1) = p^(e-1) * (p-1) *)
Lemma euler_phi_prime_pow :
  forall (p e : nat),
    prime (Z.of_nat p) ->
    (1 <= e)%nat ->
    euler_phi (p ^ e) = (p ^ (e - 1) * (p - 1))%nat.
Proof.
  intros p e Hprime He.
  assert (Hp : (0 < p)%nat) by (apply prime_ge_2 in Hprime; lia).
  assert (Hpe_pos : (0 < p ^ e)%nat).
  { generalize e. intro n. induction n as [| n' IHn'].
    - exact (Nat.lt_0_succ 0).
    - simpl. apply (proj2 (Nat.lt_0_mul' p (p^n'))). split. exact Hp. exact IHn'. }
  unfold euler_phi.
  (* gcd = 1 と k mod p ≠ 0 の等価性を使ってフィルタを書き換える *)
  assert (Hfilter_eq :
    List.filter (fun k => Z.gcd (Z.of_nat k) (Z.of_nat (p ^ e)) =? 1) (List.seq 0 (p ^ e)) =
    List.filter (fun k => negb (Nat.eqb (Nat.modulo k p) 0)) (List.seq 0 (p ^ e))).
  { apply List.filter_ext_in.
    intros k Hk_in.
    apply List.in_seq in Hk_in. simpl in Hk_in.
    destruct Hk_in as [_ Hk_lt].
    apply Bool.eq_iff_eq_true.
    rewrite Z.eqb_eq.
    rewrite Bool.negb_true_iff.
    rewrite Nat.eqb_neq.
    exact (prime_pow_coprime_iff p e k Hprime He). }
  rewrite Hfilter_eq.
  (* 補数公式 *)
  assert (Hcomp := @List.filter_length nat
    (fun k => Nat.eqb (Nat.modulo k p) 0) (List.seq 0 (p ^ e))).
  rewrite List.seq_length in Hcomp.
  assert (Hneg_len : List.length (List.filter (fun k => negb (Nat.eqb (Nat.modulo k p) 0))
                                               (List.seq 0 (p ^ e))) =
                     (Nat.sub (p ^ e) (p ^ (e - 1)))).
  { assert (Hmult_count : List.length (List.filter (fun k => Nat.eqb (Nat.modulo k p) 0)
                                                    (List.seq 0 (p ^ e)))
                          = (p ^ (e - 1))%nat).
    { replace (p ^ e)%nat with (p * p ^ (e - 1))%nat.
      - apply count_multiples_in_range. exact Hp.
      - rewrite <- Nat.pow_succ_r'. f_equal. lia. }
    lia. }
  rewrite Hneg_len.
  (* p^e - p^(e-1) = p^(e-1) * (p-1): e = S(e-1) を使って p^e = p * p^(e-1) に変換 *)
  assert (Hfact : (Nat.sub (p ^ e) (p ^ (e - 1)) = p ^ (e - 1) * (p - 1))%nat).
  { assert (He_eq : (p ^ e = p * p ^ (e - 1))%nat).
    { rewrite <- Nat.pow_succ_r'. f_equal. lia. }
    rewrite He_eq. nia. }
  exact Hfact.
Qed.

(** 補助補題: 異なる素数の冪は互いに素。
    prime p, prime q, p <> q → Nat.gcd (p^e) (q^f) = 1。 *)
Lemma prime_pow_coprime_distinct :
  forall (p q e f : nat),
    prime (Z.of_nat p) ->
    prime (Z.of_nat q) ->
    p <> q ->
    Nat.gcd (p ^ e) (q ^ f) = 1%nat.
Proof.
  intros p q e f Hpp Hpq Hpne.
  (* Step 1: Z.gcd (Z.of_nat p) (Z.of_nat q) = 1 *)
  assert (Hcop_pq : Z.gcd (Z.of_nat p) (Z.of_nat q) = 1).
  { assert (Hnotdvd : ~ (Z.of_nat p | Z.of_nat q)).
    { intro Hdvd.
      destruct (prime_divisors _ Hpq _ Hdvd) as [H | [H | [H | H]]].
      - apply prime_ge_2 in Hpp. lia.
      - apply prime_ge_2 in Hpp. lia.
      - apply Nat2Z.inj in H. exact (Hpne H).
      - apply prime_ge_2 in Hpp. apply prime_ge_2 in Hpq. lia. }
    apply Zis_gcd_gcd. { lia. }
    apply prime_rel_prime; assumption. }
  (* Step 2: Z.gcd (Z.of_nat (p^e)) (Z.of_nat (q^f)) = 1 *)
  assert (Hcop_pow : Z.gcd (Z.of_nat (p ^ e)) (Z.of_nat (q ^ f)) = 1).
  { rewrite Nat2Z.inj_pow, Nat2Z.inj_pow.
    apply Z.coprime_pow_l. { apply Nat2Z.is_nonneg. }
    apply Z.coprime_pow_r. { apply Nat2Z.is_nonneg. }
    exact Hcop_pq. }
  (* Step 3: Nat.gcd (p^e) (q^f) = 1 *)
  assert (Hd_dvd_l : (Z.of_nat (Nat.gcd (p^e) (q^f)) | Z.of_nat (p^e))).
  { destruct (Nat.gcd_divide_l (p^e) (q^f)) as [k Hk].
    exists (Z.of_nat k). rewrite <- Nat2Z.inj_mul. f_equal. lia. }
  assert (Hd_dvd_r : (Z.of_nat (Nat.gcd (p^e) (q^f)) | Z.of_nat (q^f))).
  { destruct (Nat.gcd_divide_r (p^e) (q^f)) as [k Hk].
    exists (Z.of_nat k). rewrite <- Nat2Z.inj_mul. f_equal. lia. }
  assert (Hd_dvd_1 : (Z.of_nat (Nat.gcd (p^e) (q^f)) | 1)).
  { rewrite <- Hcop_pow. apply Z.gcd_greatest; [exact Hd_dvd_l | exact Hd_dvd_r]. }
  apply Nat2Z.inj. simpl.
  destruct (Z.divide_1_r _ Hd_dvd_1) as [H | H].
  - exact H.
  - pose proof (Nat2Z.is_nonneg (Nat.gcd (p^e) (q^f))). lia.
Qed.

(** 補助補題: gcd(a,c)=1 かつ gcd(b,c)=1 ならば gcd(a*b,c)=1 (Nat レベル)。
    証明: d = gcd(a*b,c) とおき、d | b を Gauss の補題で導き、d | gcd(b,c)=1 を示す。 *)
Lemma nat_gcd_mul_coprime : forall a b c : nat,
  Nat.gcd a c = 1%nat -> Nat.gcd b c = 1%nat -> Nat.gcd (a * b) c = 1%nat.
Proof.
  intros a b c Hac Hbc.
  set (d := Nat.gcd (a * b) c).
  assert (Hd_dvd_c : Nat.divide d c) by apply Nat.gcd_divide_r.
  assert (Hd_dvd_ab : Nat.divide d (a * b)) by apply Nat.gcd_divide_l.
  assert (Hda : Nat.gcd d a = 1%nat).
  { apply Nat.divide_1_r.
    assert (H : Nat.divide (Nat.gcd d a) (Nat.gcd a c)).
    { apply Nat.gcd_greatest.
      - apply Nat.gcd_divide_r.
      - apply Nat.divide_trans with d.
        + apply Nat.gcd_divide_l.
        + exact Hd_dvd_c. }
    rewrite Hac in H. exact H. }
  assert (Hd_dvd_b : Nat.divide d b).
  { apply Nat.gauss with a.
    - destruct Hd_dvd_ab as [k Hk]. exists k. lia.
    - exact Hda. }
  unfold d.
  apply Nat.divide_1_r.
  assert (H : Nat.divide (Nat.gcd (a * b) c) (Nat.gcd b c)).
  { apply Nat.gcd_greatest.
    - exact Hd_dvd_b.
    - apply Nat.gcd_divide_r. }
  rewrite Hbc in H. exact H.
Qed.

(** 主定理: n = p^e * q^f * r^g (p, q, r は異なる素数) のとき
    φ(n) = p^(e-1)(p-1) * q^(f-1)(q-1) * r^(g-1)(r-1)。
    証明:
      1. prime_pow_coprime_distinct で gcd(p^e, q^f) = 1、gcd(p^e*q^f, r^g) = 1 を示す。
      2. euler_phi_mul を 2 回適用して乗法性を導く。
      3. euler_phi_prime_pow を 3 回適用して各因子の公式を得る。
      4. ring で等式を整理する。 *)
Theorem euler_phi_three_prime_powers :
  forall (p q r e f g : nat),
    prime (Z.of_nat p) ->
    prime (Z.of_nat q) ->
    prime (Z.of_nat r) ->
    p <> q -> q <> r -> p <> r ->
    (1 <= e)%nat -> (1 <= f)%nat -> (1 <= g)%nat ->
    euler_phi (p ^ e * q ^ f * r ^ g) =
      (p ^ (e - 1) * (p - 1) * q ^ (f - 1) * (q - 1) * r ^ (g - 1) * (r - 1))%nat.
Proof.
  intros p q r e f g Hprime Hqprime Hrprime Hpq Hqr Hpr He Hf Hg.
  assert (Hpn : (2 <= p)%nat) by (apply prime_ge_2 in Hprime; lia).
  assert (Hqn : (2 <= q)%nat) by (apply prime_ge_2 in Hqprime; lia).
  assert (Hrn : (2 <= r)%nat) by (apply prime_ge_2 in Hrprime; lia).
  (* 各冪は 1 より大: p^e >= p^1 = p >= 2 > 1 *)
  assert (Hpe_ge : (1 < p ^ e)%nat).
  { apply Nat.lt_le_trans with p; [lia |].
    apply Nat.le_trans with (p ^ 1)%nat.
    + rewrite Nat.pow_1_r. lia.
    + apply Nat.pow_le_mono_r; lia. }
  assert (Hqf_ge : (1 < q ^ f)%nat).
  { apply Nat.lt_le_trans with q; [lia |].
    apply Nat.le_trans with (q ^ 1)%nat.
    + rewrite Nat.pow_1_r. lia.
    + apply Nat.pow_le_mono_r; lia. }
  assert (Hrg_ge : (1 < r ^ g)%nat).
  { apply Nat.lt_le_trans with r; [lia |].
    apply Nat.le_trans with (r ^ 1)%nat.
    + rewrite Nat.pow_1_r. lia.
    + apply Nat.pow_le_mono_r; lia. }
  assert (Hpeqf_ge : (1 < p ^ e * q ^ f)%nat) by nia.
  (* 異なる素数の冪は互いに素 *)
  assert (Hcop_pq : Nat.gcd (p ^ e) (q ^ f) = 1%nat)
    by (apply prime_pow_coprime_distinct; [exact Hprime | exact Hqprime | exact Hpq]).
  assert (Hcop_pr : Nat.gcd (p ^ e) (r ^ g) = 1%nat)
    by (apply prime_pow_coprime_distinct; [exact Hprime | exact Hrprime | exact Hpr]).
  assert (Hcop_qr : Nat.gcd (q ^ f) (r ^ g) = 1%nat)
    by (apply prime_pow_coprime_distinct; [exact Hqprime | exact Hrprime | exact Hqr]).
  (* gcd(p^e * q^f, r^g) = 1: nat_gcd_mul_coprime を使う *)
  assert (Hcop_pqr : Nat.gcd (p ^ e * q ^ f) (r ^ g) = 1%nat).
  { apply nat_gcd_mul_coprime; [exact Hcop_pr | exact Hcop_qr]. }
  (* euler_phi 乗法性の 2 回適用 *)
  rewrite (euler_phi_mul (p ^ e * q ^ f) (r ^ g) Hpeqf_ge Hrg_ge Hcop_pqr).
  rewrite (euler_phi_mul (p ^ e) (q ^ f) Hpe_ge Hqf_ge Hcop_pq).
  (* euler_phi_prime_pow を 3 回適用 *)
  rewrite (euler_phi_prime_pow p e Hprime He).
  rewrite (euler_phi_prime_pow q f Hqprime Hf).
  rewrite (euler_phi_prime_pow r g Hrprime Hg).
  nia.
Qed.

(* ===================================================================== *)
(*  環 (Ring) と体 (Field) の定義                                          *)
(* ===================================================================== *)

(** 環 (Ring):
    集合 R に加法、乗法の二項演算と零元 0、加法逆元、乗法単位元 1 が
    定義されており、以下の公理を満たすとき R を環という。

    加法公理 (可換群):
      - 結合律: a+b+c = a+(b+c)
      - 可換律: a+b = b+a
      - 左単位元: 0+a = a
      - 左逆元: -a+a = 0

    乗法公理 (モノイド):
      - 結合律: a*b*c = a*(b*c)
      - 左単位元: 1*a = a
      - 右単位元: a*1 = a

    分配法則:
      - 左分配: a*(b+c) = a*b + a*c
      - 右分配: (a+b)*c = a*c + b*c

    注意: 右単位元・右逆元は導出可能だが、使いやすさのため右単位元は公理に含める。
    加法右逆元 a+(-a)=0 は補題 ring_add_neg_r で証明する。  *)

Record Ring : Type := {
  ring_carrier : Type;

  ring_add : ring_carrier -> ring_carrier -> ring_carrier;
  ring_zero : ring_carrier;
  ring_neg  : ring_carrier -> ring_carrier;

  ring_mul  : ring_carrier -> ring_carrier -> ring_carrier;
  ring_one  : ring_carrier;

  (* 加法公理: 可換群 *)
  ring_add_assoc : forall a b c : ring_carrier,
    ring_add (ring_add a b) c = ring_add a (ring_add b c);
  ring_add_comm  : forall a b : ring_carrier,
    ring_add a b = ring_add b a;
  ring_add_zero_l : forall a : ring_carrier,
    ring_add ring_zero a = a;
  ring_add_neg_l  : forall a : ring_carrier,
    ring_add (ring_neg a) a = ring_zero;

  (* 乗法公理: モノイド *)
  ring_mul_assoc : forall a b c : ring_carrier,
    ring_mul (ring_mul a b) c = ring_mul a (ring_mul b c);
  ring_mul_one_l : forall a : ring_carrier,
    ring_mul ring_one a = a;
  ring_mul_one_r : forall a : ring_carrier,
    ring_mul a ring_one = a;

  (* 分配法則 *)
  ring_distr_l : forall a b c : ring_carrier,
    ring_mul a (ring_add b c) = ring_add (ring_mul a b) (ring_mul a c);
  ring_distr_r : forall a b c : ring_carrier,
    ring_mul (ring_add a b) c = ring_add (ring_mul a c) (ring_mul b c)
}.

(** 環の基本補題: 加法右単位元
    証明: 可換律と左単位元から。 *)
Lemma ring_add_zero_r : forall (R : Ring) (a : ring_carrier R),
  ring_add R a (ring_zero R) = a.
Proof.
  intros R a.
  rewrite ring_add_comm.
  apply ring_add_zero_l.
Qed.

(** 環の基本補題: 加法右逆元
    証明: 可換律と左逆元から。 *)
Lemma ring_add_neg_r : forall (R : Ring) (a : ring_carrier R),
  ring_add R a (ring_neg R a) = ring_zero R.
Proof.
  intros R a.
  rewrite ring_add_comm.
  apply ring_add_neg_l.
Qed.

(** 環の基本補題: 左キャンセル則
    a+b = a+c → b = c
    証明: 両辺の左から (-a) を加える。 *)
Lemma ring_add_cancel_l : forall (R : Ring) (a b c : ring_carrier R),
  ring_add R a b = ring_add R a c -> b = c.
Proof.
  intros R a b c H.
  assert (Hbc : ring_add R (ring_neg R a) (ring_add R a b) =
                ring_add R (ring_neg R a) (ring_add R a c)).
  { rewrite H. reflexivity. }
  rewrite <- ring_add_assoc, <- ring_add_assoc in Hbc.
  rewrite ring_add_neg_l, ring_add_zero_l, ring_add_zero_l in Hbc.
  exact Hbc.
Qed.

(** 環の基本補題: 零元の乗法吸収 (左)
    0 * a = 0
    証明: 0*a + 0*a = (0+0)*a = 0*a+0 より、左キャンセル則で 0*a = 0。 *)
Lemma ring_mul_zero_l : forall (R : Ring) (a : ring_carrier R),
  ring_mul R (ring_zero R) a = ring_zero R.
Proof.
  intros R a.
  apply (ring_add_cancel_l R (ring_mul R (ring_zero R) a)).
  rewrite <- ring_distr_r.
  rewrite ring_add_zero_l.
  rewrite ring_add_zero_r.
  reflexivity.
Qed.

(** 環の基本補題: 零元の乗法吸収 (右)
    a * 0 = 0
    証明: a*0 + a*0 = a*(0+0) = a*0+0 より、左キャンセル則で a*0 = 0。 *)
Lemma ring_mul_zero_r : forall (R : Ring) (a : ring_carrier R),
  ring_mul R a (ring_zero R) = ring_zero R.
Proof.
  intros R a.
  apply (ring_add_cancel_l R (ring_mul R a (ring_zero R))).
  rewrite <- ring_distr_l.
  rewrite ring_add_zero_l.
  rewrite ring_add_zero_r.
  reflexivity.
Qed.

(** 環の基本補題: 加法逆元の冪等性
    -(-a) = a
    証明: (-(-a)) + (-a) = 0 = a + (-a) より、左キャンセル則を適用。 *)
Lemma ring_neg_neg : forall (R : Ring) (a : ring_carrier R),
  ring_neg R (ring_neg R a) = a.
Proof.
  intros R a.
  apply (ring_add_cancel_l R (ring_neg R a)).
  rewrite ring_add_neg_r.
  rewrite ring_add_neg_l.
  reflexivity.
Qed.

(** 環の基本補題: 加法逆元と乗法 (左)
    (-a) * b = -(a * b)
    証明: (-a)*b + a*b = ((-a)+a)*b = 0*b = 0 より、逆元の一意性から。 *)
Lemma ring_neg_mul_l : forall (R : Ring) (a b : ring_carrier R),
  ring_mul R (ring_neg R a) b = ring_neg R (ring_mul R a b).
Proof.
  intros R a b.
  apply (ring_add_cancel_l R (ring_mul R a b)).
  rewrite ring_add_neg_r.
  rewrite <- ring_distr_r.
  rewrite ring_add_neg_r.
  apply ring_mul_zero_l.
Qed.

(** 環の基本補題: 加法逆元と乗法 (右)
    a * (-b) = -(a * b)
    証明: a*(-b) + a*b = a*((-b)+b) = a*0 = 0 より、逆元の一意性から。 *)
Lemma ring_neg_mul_r : forall (R : Ring) (a b : ring_carrier R),
  ring_mul R a (ring_neg R b) = ring_neg R (ring_mul R a b).
Proof.
  intros R a b.
  apply (ring_add_cancel_l R (ring_mul R a b)).
  rewrite ring_add_neg_r.
  rewrite <- ring_distr_l.
  rewrite ring_add_neg_r.
  apply ring_mul_zero_r.
Qed.

(** 環の基本補題: 差がゼロ ↔ 等しい
    a - b = 0 ↔ a = b  (ここで a - b は ring_add R a (ring_neg R b))

    証明の方針:
      ← : a = b に代入して ring_add_neg_r を適用。
      → : 両辺に b を加算。ring_add_assoc, ring_add_neg_l, ring_add_zero_r,
          ring_add_zero_l で a = b を導く。  *)
Lemma ring_sub_zero_iff_eq : forall (R : Ring) (a b : ring_carrier R),
  ring_add R a (ring_neg R b) = ring_zero R <-> a = b.
Proof.
  intros R a b.
  split.
  - intros H.
    assert (H2 : ring_add R (ring_add R a (ring_neg R b)) b =
                 ring_add R (ring_zero R) b).
    { rewrite H. reflexivity. }
    rewrite ring_add_assoc in H2.
    rewrite ring_add_neg_l in H2.
    rewrite ring_add_zero_r in H2.
    rewrite ring_add_zero_l in H2.
    exact H2.
  - intros H.
    subst.
    apply ring_add_neg_r.
Qed.

(** 体 (Field):
    体とは可換環であって、零元以外のすべての元が乗法逆元を持つものをいう。

    具体的には、環 R に対して以下の条件を追加したもの:
      1. 乗法可換律: ∀ a b, a * b = b * a
      2. 非零元の乗法逆元の存在: ∀ x ≠ 0, ∃ inv(x) s.t. inv(x) * x = 1
      3. 零元と単位元の相異: 1 ≠ 0

    Rocq 実装の方針:
      - field_inv は全域関数として定義 (field_inv 0 は任意の値)
      - 逆元の性質は非零の仮定のもとで述べる
      - `:>` により Field を Ring として直接使用できる  *)

Record Field : Type := {
  field_ring :> Ring;

  field_inv : ring_carrier field_ring -> ring_carrier field_ring;

  (* 乗法可換律 *)
  field_mul_comm : forall a b : ring_carrier field_ring,
    ring_mul field_ring a b = ring_mul field_ring b a;

  (* 非零元の左逆元 *)
  field_inv_l : forall x : ring_carrier field_ring,
    x <> ring_zero field_ring ->
    ring_mul field_ring (field_inv x) x = ring_one field_ring;

  (* 単位元と零元の相異 *)
  field_one_ne_zero : ring_one field_ring <> ring_zero field_ring
}.

(** 体の基本補題: 右逆元
    x ≠ 0 → x * inv(x) = 1
    証明: 可換律と左逆元から。 *)
Lemma field_inv_r : forall (F : Field) (x : ring_carrier F),
  x <> ring_zero F ->
  ring_mul F x (field_inv F x) = ring_one F.
Proof.
  intros F x Hx.
  rewrite field_mul_comm.
  apply field_inv_l.
  exact Hx.
Qed.

(** 体の基本補題: 逆元の非零性
    x ≠ 0 → inv(x) ≠ 0
    証明: inv(x) = 0 と仮定すると inv(x)*x = 0*x = 0 だが、
    field_inv_l より inv(x)*x = 1。1 ≠ 0 に矛盾。 *)
Lemma field_inv_nonzero : forall (F : Field) (x : ring_carrier F),
  x <> ring_zero F ->
  field_inv F x <> ring_zero F.
Proof.
  intros F x Hx Hinv.
  pose proof (field_inv_l F x Hx) as H.
  rewrite Hinv in H.
  rewrite ring_mul_zero_l in H.
  exact (field_one_ne_zero F (eq_sym H)).
Qed.

(** 体の基本補題: 零因子なし
    a * b = 0 → a = 0 ∨ b = 0
    証明: a ≠ 0 を仮定し、両辺の左から inv(a) を掛けると
    inv(a)*(a*b) = (inv(a)*a)*b = 1*b = b = inv(a)*0 = 0。 *)
Lemma field_no_zero_divisors : forall (F : Field) (a b : ring_carrier F),
  ring_mul F a b = ring_zero F ->
  a = ring_zero F \/ b = ring_zero F.
Proof.
  intros F a b Hab.
  destruct (classic (a = ring_zero F)) as [Ha | Ha].
  - left. exact Ha.
  - right.
    pose proof (field_inv_l F a Ha) as Hinva.
    assert (H : ring_mul F (field_inv F a) (ring_mul F a b) = ring_zero F).
    { rewrite Hab. apply ring_mul_zero_r. }
    rewrite <- ring_mul_assoc in H.
    rewrite Hinva in H.
    rewrite ring_mul_one_l in H.
    exact H.
Qed.

(** 体の基本補題: 乗法左キャンセル則
    a ≠ 0 → a*b = a*c → b = c
    証明: a*b - a*c = 0 → a*(b-c) = 0 → b-c = 0 → b = c。
    ここでは field_no_zero_divisors を直接使う。 *)
Lemma field_mul_cancel_l : forall (F : Field) (a b c : ring_carrier F),
  a <> ring_zero F ->
  ring_mul F a b = ring_mul F a c ->
  b = c.
Proof.
  intros F a b c Ha Hbc.
  pose proof (field_inv_l F a Ha) as Hinva.
  assert (H1 : ring_mul F (field_inv F a) (ring_mul F a b) =
               ring_mul F (field_inv F a) (ring_mul F a c)).
  { rewrite Hbc. reflexivity. }
  rewrite <- ring_mul_assoc, <- ring_mul_assoc in H1.
  rewrite Hinva, ring_mul_one_l, ring_mul_one_l in H1.
  exact H1.
Qed.

(** 体における除法:
    a / b := a * inv(b)
    b ≠ 0 のときのみ意味を持つ (全域関数として定義)。 *)
Definition field_div (F : Field) (a b : ring_carrier F) : ring_carrier F :=
  ring_mul F a (field_inv F b).

(** =====================================================================
    具体例: Z/pZ は素数 p のとき体である (znz_p_field)
    =====================================================================

    証明の方針:
      - 加法: znz_group p が Ring の加法構造を与える
      - 乗法: Z 上の乗法 mod p を定義し、結合律・分配法則を示す
      - 逆元: p が素数なら gcd(a, p) = 1 (a ≢ 0) なので
              znz_coprime_bezout_inv より Bezout 係数が逆元になる
      - 1 ≠ 0: p ≥ 2 なので 1 mod p ≠ 0 mod p  *)

(** 補助補題: 素数 p に対して gcd(a mod p, p) = 1 (a mod p ≠ 0)。
    証明: Znumtheory の prime_rel_prime を使い、
    a ≢ 0 (mod p) ならば p ∤ a → gcd(a, p) = 1。 *)
Lemma znz_prime_nonzero_coprime : forall (p : nat) (a : Z),
  prime (Z.of_nat p) ->
  a mod Z.of_nat p <> 0 ->
  Z.gcd (a mod Z.of_nat p) (Z.of_nat p) = 1.
Proof.
  intros p a Hprime Hne.
  set (r := a mod Z.of_nat p).
  assert (Hp2 : (2 <= p)%nat) by (apply prime_ge_2 in Hprime; lia).
  assert (Hbound : 0 <= r /\ r < Z.of_nat p).
  { unfold r. split; apply Z.mod_pos_bound; lia. }
  destruct Hbound as [Hr_pos Hr_lt].
  apply Zis_gcd_gcd. { lia. }
  apply Zis_gcd_sym.
  apply (prime_rel_prime (Z.of_nat p) Hprime).
  intro Hdvd.
  apply Hne.
  destruct Hdvd as [k Hk].
  assert (k = 0) by nia.
  lia.
Qed.

(** Z/pZ の乗法逆元の値 (epsilon による定義):
    `znz_units_inv_val` と同構造だが、引数に gcd 条件を要求しない
    ({x | 0<=x<p} のみ)。素数条件のもとで非零元に対して逆元を取り出す。
    非零でない場合 (a = 0) は epsilon の結果が任意の値を返す可能性があるが、
    `field_inv_l` では非零仮定のもとでしか使わないため問題ない。  *)
Definition znz_field_inv_val (p : nat)
    (a : {x : Z | 0 <= x < Z.of_nat p}) : Z :=
  epsilon (inhabits 0%Z)
    (fun b => 0 <= b < Z.of_nat p /\ cong p (proj1_sig a * b) 1).

(** Z/pZ の乗法逆元の性質:
    p が素数で proj1_sig a ≠ 0 ならば、
    znz_field_inv_val p a は [0, p) の範囲にあり、
    cong p (proj1_sig a * znz_field_inv_val p a) 1 が成立する。

    証明方針:
      1. Z.mod_small と sigma 型の範囲条件より proj1_sig a mod p = proj1_sig a
      2. znz_prime_nonzero_coprime → Z.gcd (proj1_sig a) p = 1
      3. znz_coprime_bezout_inv → ∃ b ∈ [0,p), cong p (proj1_sig a * b) 1
      4. epsilon_spec でその b が znz_field_inv_val の値であることを示す  *)
Lemma znz_field_inv_spec : forall (p : nat) (Hp : prime (Z.of_nat p))
    (a : {x : Z | 0 <= x < Z.of_nat p}),
  proj1_sig a <> 0 ->
  0 <= znz_field_inv_val p a < Z.of_nat p /\
  cong p (proj1_sig a * znz_field_inv_val p a) 1.
Proof.
  intros p Hp a Ha.
  assert (Hp2 : (2 <= p)%nat) by (apply prime_ge_2 in Hp; lia).
  unfold znz_field_inv_val.
  apply epsilon_spec.
  assert (Ha_range : 0 <= proj1_sig a < Z.of_nat p) by exact (proj2_sig a).
  assert (Hgcd : Z.gcd (proj1_sig a) (Z.of_nat p) = 1).
  { rewrite <- (Z.mod_small (proj1_sig a) (Z.of_nat p)) by exact Ha_range.
    apply znz_prime_nonzero_coprime.
    - exact Hp.
    - rewrite Z.mod_small by exact Ha_range.
      exact Ha. }
  destruct (znz_coprime_bezout_inv p (ltac:(lia)) (proj1_sig a) Ha_range Hgcd)
    as [b [Hb_range [Hb_cong _]]].
  exact (ex_intro _ b (conj Hb_range Hb_cong)).
Qed.

(** Z/pZ の環 (Ring) 構造 (p は素数):
    台集合 {x : Z | 0 <= x < p} に加法と乗法を定義する。
    加法は znz_group と同じ。乗法は znz_units_group と同じパターン。  *)
Definition znz_p_ring (p : nat) (Hp : prime (Z.of_nat p)) : Ring.
Proof.
  assert (Hp2 : (2 <= p)%nat) by (apply prime_ge_2 in Hp; lia).
  assert (HN : 0 < Z.of_nat p) by lia.
  refine {|
    ring_carrier := {x : Z | 0 <= x < Z.of_nat p};
    ring_add := fun a b =>
      exist _ ((proj1_sig a + proj1_sig b) mod Z.of_nat p)
              (Z.mod_pos_bound _ _ HN);
    ring_zero := exist _ 0 (conj (Z.le_refl 0) HN);
    ring_neg := fun a =>
      exist _ ((- proj1_sig a) mod Z.of_nat p)
              (Z.mod_pos_bound _ _ HN);
    ring_mul := fun a b =>
      exist _ ((proj1_sig a * proj1_sig b) mod Z.of_nat p)
              (Z.mod_pos_bound _ _ HN);
    ring_one := exist _ (1 mod Z.of_nat p)
                        (Z.mod_pos_bound _ _ HN)
  |}.
  (* ring_add_assoc *)
  - intros [a Ha] [b Hb] [c Hc]. apply sig_eq. simpl.
    rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Z.add_assoc. reflexivity.
  (* ring_add_comm *)
  - intros [a Ha] [b Hb]. apply sig_eq. simpl.
    rewrite Z.add_comm. reflexivity.
  (* ring_add_zero_l *)
  - intros [a Ha]. apply sig_eq. simpl.
    apply Z.mod_small. exact Ha.
  (* ring_add_neg_l *)
  - intros [a Ha]. apply sig_eq. simpl.
    rewrite Zplus_mod_idemp_l, Z.add_opp_diag_l. apply Zmod_0_l.
  (* ring_mul_assoc *)
  - intros [a Ha] [b Hb] [c Hc]. apply sig_eq. simpl.
    rewrite Zmult_mod_idemp_r, Zmult_mod_idemp_l, Z.mul_assoc. reflexivity.
  (* ring_mul_one_l: (1 mod p * a) mod p = a *)
  - intros [a Ha]. apply sig_eq. simpl.
    rewrite Zmult_mod_idemp_l, Z.mul_1_l. apply Z.mod_small. exact Ha.
  (* ring_mul_one_r: (a * (1 mod p)) mod p = a *)
  - intros [a Ha]. apply sig_eq. simpl.
    rewrite Zmult_mod_idemp_r, Z.mul_1_r. apply Z.mod_small. exact Ha.
  (* ring_distr_l *)
  - intros [a Ha] [b Hb] [c Hc]. apply sig_eq. simpl.
    rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r.
    rewrite Z.mul_add_distr_l. reflexivity.
  (* ring_distr_r *)
  - intros [a Ha] [b Hb] [c Hc]. apply sig_eq. simpl.
    rewrite Zmult_mod_idemp_l, Zplus_mod_idemp_l, Zplus_mod_idemp_r.
    rewrite Z.mul_add_distr_r. reflexivity.
Defined.

(** 素数 p のとき Z/pZ は体である。
    台集合は {x : Z | 0 <= x < Z.of_nat p} (sigma 型、znz_group と同じ)。
    Ring 部分は znz_p_ring を使う。  *)
Definition znz_p_field (p : nat) (Hp : prime (Z.of_nat p)) : Field.
Proof.
  assert (Hp2 : (2 <= p)%nat) by (apply prime_ge_2 in Hp; lia).
  assert (HN : 0 < Z.of_nat p) by lia.
  refine {|
    field_ring := znz_p_ring p Hp;
    field_inv  := fun a =>
      match Z.eq_dec (proj1_sig a) 0 with
      | left _   => exist (fun x => 0 <= x < Z.of_nat p) 0 (conj (Z.le_refl 0) HN)
      | right Ha => exist (fun x => 0 <= x < Z.of_nat p) (znz_field_inv_val p a)
                         (proj1 (znz_field_inv_spec p Hp a Ha))
      end;
    field_mul_comm  := _;
    field_inv_l     := _;
    field_one_ne_zero := _
  |}.
  (* field_mul_comm *)
  - intros [a Ha] [b Hb]. apply sig_eq. simpl.
    rewrite Z.mul_comm. reflexivity.
  (* field_inv_l: x ≠ 0 → inv(x) * x = 1 *)
  - intros x Hx.
    assert (Ha : proj1_sig x <> 0).
    { intro Heq. apply Hx. apply sig_eq. simpl. exact Heq. }
    destruct (znz_field_inv_spec p Hp x Ha) as [_ Hcong].
    apply sig_eq. simpl.
    destruct (Z.eq_dec (proj1_sig x) 0) as [Hc | Hc].
    + contradiction.
    + (* proj1_sig (field_inv F x) = znz_field_inv_val p x を明示的に簡約 *)
      cbn [proj1_sig].
      rewrite Z.mul_comm.
      unfold cong in Hcong. destruct Hcong as [k Hk].
      assert (Heq : proj1_sig x * znz_field_inv_val p x = Z.of_nat p * k + 1) by lia.
      rewrite Heq.
      replace (Z.of_nat p * k + 1) with (1 + k * Z.of_nat p) by ring.
      rewrite Z.mod_add by lia.
      reflexivity.
  (* field_one_ne_zero: 1 mod p ≠ 0 *)
  - intro Heq.
    assert (H : proj1_sig (ring_one (znz_p_ring p Hp)) = proj1_sig (ring_zero (znz_p_ring p Hp))).
    { rewrite Heq. reflexivity. }
    simpl in H.
    rewrite Z.mod_small in H by lia.
    lia.
Defined.

(** =====================================================================
    体上の1次方程式の唯一解定理
    =====================================================================

    体 F 上の1次方程式 ax + b = 0 (a ≠ 0) はちょうど1つの解を持つ。
    特に、Fp = Z/pZ (p 素数) に適用することで Fp 上の命題を得る。  *)

(** 補題: 解の構成
    a ≠ 0 のとき x₀ = -(inv(a) * b) は a*x₀ + b = 0 を満たす。

    証明の方針:
      a * (-(inv(a) * b)) + b
      = -(a * (inv(a) * b)) + b    [ring_neg_mul_l]
      = -((a * inv(a)) * b) + b    [← ring_mul_assoc]
      = -(1 * b) + b               [field_inv_r]
      = -b + b                     [ring_mul_one_l]
      = 0                          [ring_add_neg_l]  *)
Lemma field_linear_eq_solution : forall (F : Field) (a b : ring_carrier F),
  a <> ring_zero F ->
  ring_add F (ring_mul F a (ring_neg F (ring_mul F (field_inv F a) b))) b = ring_zero F.
Proof.
  intros F a b Ha.
  rewrite ring_neg_mul_r.
  rewrite <- ring_mul_assoc.
  rewrite field_inv_r by exact Ha.
  rewrite ring_mul_one_l.
  apply ring_add_neg_l.
Qed.

(** 補題: 解の一意性
    a ≠ 0 かつ a*x + b = 0 かつ a*y + b = 0 ならば x = y。

    証明の方針:
      1. a*x + b = 0 = a*y + b なので ring_add_cancel_l で b を消去: a*x = a*y
      2. field_mul_cancel_l で a を消去: x = y  *)
Lemma field_linear_eq_unique : forall (F : Field) (a b x y : ring_carrier F),
  a <> ring_zero F ->
  ring_add F (ring_mul F a x) b = ring_zero F ->
  ring_add F (ring_mul F a y) b = ring_zero F ->
  x = y.
Proof.
  intros F a b x y Ha Hx Hy.
  apply (field_mul_cancel_l F a).
  - exact Ha.
  - apply (ring_add_cancel_l F b).
    rewrite (ring_add_comm F b), (ring_add_comm F b).
    rewrite Hx, Hy.
    reflexivity.
Qed.

(** 主定理: 体上の1次方程式の唯一解
    体 F 上の方程式 ax + b = 0 (a ≠ 0) はちょうど1つの解を持つ。

    証明の方針:
      - 解 x₀ = -(inv(a) * b) を witness として exists! に渡す
      - 存在: field_linear_eq_solution
      - 一意性: field_linear_eq_unique  *)
Theorem field_linear_eq_unique_solution : forall (F : Field) (a b : ring_carrier F),
  a <> ring_zero F ->
  exists! x : ring_carrier F,
    ring_add F (ring_mul F a x) b = ring_zero F.
Proof.
  intros F a b Ha.
  exists (ring_neg F (ring_mul F (field_inv F a) b)).
  split.
  - apply field_linear_eq_solution. exact Ha.
  - intros y Hy.
    apply (field_linear_eq_unique F a b).
    + exact Ha.
    + apply field_linear_eq_solution. exact Ha.
    + exact Hy.
Qed.

(** 系: Fp 上の1次方程式の唯一解
    素数 p のとき Fp = Z/pZ 上の方程式 ax + b = 0 (a ≠ 0) は
    ちょうど1つの解を持つ。

    証明の方針: field_linear_eq_unique_solution を znz_p_field に適用。  *)
Corollary fp_linear_eq_unique_solution :
  forall (p : nat) (Hp : prime (Z.of_nat p))
         (a b : ring_carrier (znz_p_field p Hp)),
  a <> ring_zero (znz_p_field p Hp) ->
  exists! x : ring_carrier (znz_p_field p Hp),
    ring_add (znz_p_field p Hp) (ring_mul (znz_p_field p Hp) a x) b =
    ring_zero (znz_p_field p Hp).
Proof.
  intros p Hp a b Ha.
  apply field_linear_eq_unique_solution.
  exact Ha.
Qed.

(** =====================================================================
    体上の多項式と剰余の定理 (Polynomial Remainder Theorem over a Field)
    =====================================================================

    多項式の表現: 係数リスト（小端表現）
      [c0, c1, ..., cn] = c0 + c1*x + c2*x^2 + ... + cn*x^n

    ホーナー法:
      eval [] x       = 0
      eval (c::cs) x  = c + x * eval cs x

    剰余の定理:
      任意の多項式 f と体の元 a に対し、商多項式 q が存在して
        f(x) = (x - a) * q(x) + f(a)
    が恒等的に成立する。

    証明の方針:
      合成除算 (synthetic division) によって商多項式 q を陽に定義し、
      リスト帰納法でこの等式を証明する。                                     *)

(** ホーナー法による多項式評価
    体 F 上の多項式 f を点 x で評価する。
    eval [] x       = 0
    eval (c::cs) x  = c + x * eval cs x  *)
Fixpoint poly_eval (F : Field) (f : list (ring_carrier F)) (x : ring_carrier F)
  : ring_carrier F :=
  match f with
  | [] => ring_zero F
  | c :: cs => ring_add F c (ring_mul F x (poly_eval F cs x))
  end.

(** 合成除算：f を (x - a) で割ったときの商多項式を返す。
    div [] a      = []
    div [c] a     = []
    div (c::cs) a = eval cs a :: div cs a   (cs が空でない場合)  *)
Fixpoint poly_synthetic_div (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F)
  : list (ring_carrier F) :=
  match f with
  | [] => []
  | _ :: cs =>
    match cs with
    | [] => []
    | _ => poly_eval F cs a :: poly_synthetic_div F cs a
    end
  end.

(** 補題: poly_eval の空リストケース
    証明: 定義から直ちに。 *)
Lemma poly_eval_nil : forall (F : Field) (x : ring_carrier F),
  poly_eval F [] x = ring_zero F.
Proof.
  intros F x. reflexivity.
Qed.

(** 補題: poly_eval のコンスケース
    証明: 定義から直ちに。 *)
Lemma poly_eval_cons : forall (F : Field) (c : ring_carrier F)
    (cs : list (ring_carrier F)) (x : ring_carrier F),
  poly_eval F (c :: cs) x = ring_add F c (ring_mul F x (poly_eval F cs x)).
Proof.
  intros F c cs x. reflexivity.
Qed.

(** 補題: poly_eval の単一係数ケース
    poly_eval F [c] x = c

    証明の方針: poly_eval_cons, poly_eval_nil, ring_mul_zero_r, ring_add_zero_r を順に適用。  *)
Lemma poly_eval_single : forall (F : Field) (c x : ring_carrier F),
  poly_eval F [c] x = c.
Proof.
  intros F c x.
  rewrite poly_eval_cons.
  rewrite poly_eval_nil.
  rewrite ring_mul_zero_r.
  apply ring_add_zero_r.
Qed.

(** 補題: poly_synthetic_div の空リストケース
    証明: 定義から直ちに。 *)
Lemma poly_synthetic_div_nil : forall (F : Field) (a : ring_carrier F),
  poly_synthetic_div F [] a = [].
Proof.
  intros F a. reflexivity.
Qed.

(** 補題: poly_synthetic_div の1要素リストケース
    証明: 定義から直ちに。 *)
Lemma poly_synthetic_div_singleton : forall (F : Field) (c a : ring_carrier F),
  poly_synthetic_div F [c] a = [].
Proof.
  intros F c a. reflexivity.
Qed.

(** 補題: poly_synthetic_div のコンスケース（cs が空でない場合）
    div (c :: c' :: cs) a = eval (c' :: cs) a :: div (c' :: cs) a
    証明: 定義から直ちに。 *)
Lemma poly_synthetic_div_cons : forall (F : Field) (c c' : ring_carrier F)
    (cs : list (ring_carrier F)) (a : ring_carrier F),
  poly_synthetic_div F (c :: c' :: cs) a =
    poly_eval F (c' :: cs) a :: poly_synthetic_div F (c' :: cs) a.
Proof.
  intros F c c' cs a. reflexivity.
Qed.

(** 補題: 合成除算後の長さ
    (c :: cs) を (x - a) で割ったときの商の長さは cs の長さと等しい。
      length (poly_synthetic_div F (c :: cs) a) = length cs

    証明の方針: cs の構造帰納法。
      - cs = [] : poly_synthetic_div_singleton より商は [] ✓
      - cs = c' :: cs' : poly_synthetic_div_cons + change + f_equal + IH ✓  *)
Lemma poly_synthetic_div_length :
  forall (F : Field) (c : ring_carrier F) (cs : list (ring_carrier F))
         (a : ring_carrier F),
    length (poly_synthetic_div F (c :: cs) a) = length cs.
Proof.
  intros F c cs a.
  induction cs as [| c' cs' IH].
  - reflexivity.
  - rewrite poly_synthetic_div_cons.
    (* simpl length は poly_synthetic_div を展開してしまうので change を使う *)
    change (S (length (poly_synthetic_div F (c' :: cs') a)) = S (length cs')).
    f_equal. exact IH.
Qed.

(** 補題: リストの last の再帰則 (非空テール)
    t ≠ [] のとき last (h :: t) d = last t d

    証明の方針: t を destruct して、空の場合は矛盾、非空の場合は定義から直ちに。  *)
Lemma last_cons_nonempty :
  forall (A : Type) (h : A) (t : list A) (d : A),
    t <> [] ->
    last (h :: t) d = last t d.
Proof.
  intros A h t d Ht.
  destruct t.
  - contradiction.
  - reflexivity.
Qed.

(** 補題: 合成除算は先頭係数 (last 要素) を保存する
    length f ≥ 2 のとき last (poly_synthetic_div F f a) d = last f d

    証明の方針: f の長さに関する帰納法。
      - length 2 (f = [c, c']): poly_synthetic_div_cons と poly_eval_single から
          last [poly_eval F [c'] a] d = poly_eval F [c'] a = c' = last [c, c'] d
      - length n+1 ≥ 3 (f = c :: c' :: cs, cs ≠ []):
          poly_synthetic_div_cons より商は nonempty で、
          last_cons_nonempty と帰納法仮定から示す。  *)
Lemma poly_synthetic_div_last :
  forall (F : Field) (f : list (ring_carrier F)) (a d : ring_carrier F),
    (2 <= length f)%nat ->
    last (poly_synthetic_div F f a) d = last f d.
Proof.
  intros F f a d.
  induction f as [| c cs IH].
  - intro Hlen. simpl in Hlen. lia.
  - destruct cs as [| c' cs'].
    + intro Hlen. simpl in Hlen. lia.
    + intros Hlen.
      rewrite poly_synthetic_div_cons.
      destruct cs' as [| c'' cs''].
      * (* cs' = [], f = [c, c'] *)
        simpl.
        apply poly_eval_single.
      * (* cs' = c'' :: cs'', length f ≥ 3 *)
        assert (Hlen2 : (2 <= length (c' :: c'' :: cs''))%nat) by (simpl; lia).
        assert (Hdiv_nonempty : poly_synthetic_div F (c' :: c'' :: cs'') a <> []).
        { intro Hempty.
          pose proof (poly_synthetic_div_length F c' (c'' :: cs'') a) as Hk.
          rewrite Hempty in Hk. simpl in Hk. lia. }
        rewrite last_cons_nonempty by exact Hdiv_nonempty.
        rewrite IH by exact Hlen2.
        reflexivity.
Qed.

(** 補題 A: (x - a) * e + a * e = x * e
    証明:
      (x + (-a)) * e + a * e
      = x*e + (-a)*e + a*e    [ring_distr_r, ring_add_assoc]
      = x*e + -(a*e) + a*e    [ring_neg_mul_l]
      = x*e + 0               [ring_add_neg_l]
      = x*e                   [ring_add_zero_r]  *)
Lemma poly_remainder_alg_A : forall (F : Field) (a x e : ring_carrier F),
  ring_add F
    (ring_mul F (ring_add F x (ring_neg F a)) e)
    (ring_mul F a e)
  = ring_mul F x e.
Proof.
  intros F a x e.
  rewrite ring_distr_r.
  rewrite ring_neg_mul_l.
  rewrite ring_add_assoc.
  rewrite ring_add_neg_l.
  rewrite ring_add_zero_r.
  reflexivity.
Qed.

(** 補題 B: x * ((x - a) * q) = (x - a) * (x * q)
    証明:
      x * ((x-a) * q)
      = (x * (x-a)) * q    [← ring_mul_assoc]
      = ((x-a) * x) * q    [field_mul_comm]
      = (x-a) * (x * q)    [ring_mul_assoc]  *)
Lemma poly_remainder_alg_B : forall (F : Field) (a x q : ring_carrier F),
  ring_mul F x (ring_mul F (ring_add F x (ring_neg F a)) q)
  = ring_mul F (ring_add F x (ring_neg F a)) (ring_mul F x q).
Proof.
  intros F a x q.
  rewrite <- ring_mul_assoc.
  rewrite (field_mul_comm F x (ring_add F x (ring_neg F a))).
  rewrite ring_mul_assoc.
  reflexivity.
Qed.

(** 補題 CORE: 剰余定理の代数的核心
    (x-a)*(e + x*q) + a*e = x*(e + (x-a)*q)
    が恒等的に成立する。

    証明の方針:
      両辺が x*e + (x-a)*(x*q) に等しいことを示す。
      LHS: ring_distr_l, ring_add_assoc, ring_add_comm, poly_remainder_alg_A
      RHS: ring_distr_l, poly_remainder_alg_B  *)
Lemma poly_remainder_core : forall (F : Field) (a x e q : ring_carrier F),
  ring_add F
    (ring_mul F (ring_add F x (ring_neg F a)) (ring_add F e (ring_mul F x q)))
    (ring_mul F a e)
  = ring_mul F x (ring_add F e (ring_mul F (ring_add F x (ring_neg F a)) q)).
Proof.
  intros F a x e q.
  transitivity (ring_add F (ring_mul F x e)
                           (ring_mul F (ring_add F x (ring_neg F a)) (ring_mul F x q))).
  - (* LHS = x*e + (x-a)*(x*q) *)
    rewrite ring_distr_l.
    rewrite ring_add_assoc.
    rewrite (ring_add_comm F
               (ring_mul F (ring_add F x (ring_neg F a)) (ring_mul F x q))
               (ring_mul F a e)).
    rewrite <- ring_add_assoc.
    rewrite poly_remainder_alg_A.
    reflexivity.
  - (* x*e + (x-a)*(x*q) = RHS *)
    symmetry.
    rewrite ring_distr_l.
    f_equal.
    apply poly_remainder_alg_B.
Qed.

(** 主定理: 体上の多項式の剰余定理
    任意の体 F 上の多項式 f と元 a, x に対し、
      f(x) = (x - a) * q(x) + f(a)
    が成立する。ここで q = poly_synthetic_div F f a。

    証明の方針:
      f に対するリスト帰納法。
      - 空リスト: 両辺とも 0。
      - 1要素リスト [c]: 両辺とも c。
      - [c, c', ...]: 帰納法仮定と poly_remainder_core で示す。  *)
Theorem poly_remainder_theorem :
  forall (F : Field) (f : list (ring_carrier F)) (a x : ring_carrier F),
    poly_eval F f x =
    ring_add F
      (ring_mul F (ring_add F x (ring_neg F a))
                  (poly_eval F (poly_synthetic_div F f a) x))
      (poly_eval F f a).
Proof.
  intros F f a x.
  induction f as [| c cs IHcs].
  - (* f = [] *)
    simpl.
    rewrite ring_mul_zero_r.
    rewrite ring_add_zero_l.
    reflexivity.
  - (* f = c :: cs *)
    (* destruct 前に poly_eval を展開しない: auto-reduction を避けるため *)
    destruct cs as [| c' cs'].
    + (* cs = [], f = [c] *)
      (* cbn で poly_eval と poly_synthetic_div を展開して代入 *)
      cbn [poly_eval poly_synthetic_div].
      (* すべての ? * 0 を 0 に簡約 *)
      repeat rewrite ring_mul_zero_r.
      (* c + 0 = 0 + (c + 0) → ring_add_zero_l で 0 + X → X → c + 0 = c + 0 *)
      rewrite ring_add_zero_l.
      reflexivity.
    + (* cs = c' :: cs', f = c :: c' :: cs' *)
      (* LHS: poly_eval F (c :: c'::cs') x → c + x * poly_eval F (c'::cs') x *)
      rewrite poly_eval_cons.
      (* poly_synthetic_div F (c :: c'::cs') a = eval(c'::cs') a :: div(c'::cs') a *)
      rewrite poly_synthetic_div_cons.
      (* poly_eval F (eval(c'::cs') a :: div(c'::cs') a) x
           = eval(c'::cs') a + x * poly_eval F (div(c'::cs') a) x *)
      rewrite (poly_eval_cons F (poly_eval F (c' :: cs') a)
                                (poly_synthetic_div F (c' :: cs') a) x).
      (* poly_eval F (c :: c'::cs') a = c + a * poly_eval F (c'::cs') a *)
      rewrite (poly_eval_cons F c (c' :: cs') a).
      (* 帰納法仮定を適用: poly_eval F (c'::cs') x = (x-a)*q + e *)
      rewrite IHcs.
      (* e と q を set で簡略化 *)
      set (e := poly_eval F (c' :: cs') a).
      set (q := poly_eval F (poly_synthetic_div F (c' :: cs') a) x).
      (* 目標: c + x*((x-a)*q + e) = (x-a)*(e + x*q) + (c + a*e) *)
      (* (x-a)*q + e → e + (x-a)*q に並び替える *)
      rewrite (ring_add_comm F (ring_mul F (ring_add F x (ring_neg F a)) q) e).
      (* 目標: c + x*(e + (x-a)*q) = (x-a)*(e + x*q) + (c + a*e) *)
      (* 中間形 c + ((x-a)*(e + x*q) + a*e) に transitivity *)
      transitivity (ring_add F c
                     (ring_add F
                       (ring_mul F (ring_add F x (ring_neg F a))
                                   (ring_add F e (ring_mul F x q)))
                       (ring_mul F a e))).
      * (* c + x*(e + (x-a)*q) = c + ((x-a)*(e+x*q) + a*e) *)
        (* poly_remainder_core: (x-a)*(e+x*q) + a*e = x*(e + (x-a)*q) *)
        rewrite poly_remainder_core.
        reflexivity.
      * (* c + ((x-a)*(e+x*q) + a*e) = (x-a)*(e+x*q) + (c + a*e) *)
        rewrite <- ring_add_assoc.
        rewrite (ring_add_comm F c
                   (ring_mul F (ring_add F x (ring_neg F a))
                               (ring_add F e (ring_mul F x q)))).
        rewrite ring_add_assoc.
        reflexivity.
Qed.

(** 系: Fp 上の多項式の剰余定理
    素数 p のとき Fp = Z/pZ 上の多項式 f と元 a, x に対し、
      f(x) = (x - a) * q(x) + f(a)
    が成立する。

    証明の方針: poly_remainder_theorem を znz_p_field p Hp に適用。  *)
Corollary fp_remainder_theorem :
  forall (p : nat) (Hp : prime (Z.of_nat p))
         (f : list (ring_carrier (znz_p_field p Hp)))
         (a x : ring_carrier (znz_p_field p Hp)),
    poly_eval (znz_p_field p Hp) f x =
    ring_add (znz_p_field p Hp)
      (ring_mul (znz_p_field p Hp)
        (ring_add (znz_p_field p Hp) x (ring_neg (znz_p_field p Hp) a))
        (poly_eval (znz_p_field p Hp) (poly_synthetic_div (znz_p_field p Hp) f a) x))
      (poly_eval (znz_p_field p Hp) f a).
Proof.
  intros p Hp f a x.
  apply poly_remainder_theorem.
Qed.

(** 線形因子による可除性:
    多項式 f が (x - a) で割り切れるとは、商多項式 q が存在して
      ∀ x, f(x) = (x - a) * q(x)
    が成り立つことと定義する。  *)
Definition poly_divides_linear (F : Field)
    (f : list (ring_carrier F)) (a : ring_carrier F) : Prop :=
  exists q : list (ring_carrier F),
    forall x : ring_carrier F,
      poly_eval F f x =
      ring_mul F (ring_add F x (ring_neg F a)) (poly_eval F q x).

(** 補題: 根があれば線形因子で割り切れる
    f(a) = 0 ならば (x - a) | f(x)

    証明の方針:
      剰余定理より f(x) = (x - a) * q(x) + f(a)。
      f(a) = 0 を代入し ring_add_zero_r で末尾の 0 を消去すると
        f(x) = (x - a) * q(x)
      を得る。商の証拠は poly_synthetic_div F f a。  *)
Lemma poly_factor_of_root :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_eval F f a = ring_zero F ->
    poly_divides_linear F f a.
Proof.
  intros F f a Hroot.
  unfold poly_divides_linear.
  exists (poly_synthetic_div F f a).
  intros x.
  rewrite (poly_remainder_theorem F f a x).
  rewrite Hroot.
  apply ring_add_zero_r.
Qed.

(** 補題: 線形因子で割り切れれば根が存在する
    (x - a) | f(x) ならば f(a) = 0

    証明の方針:
      仮定から ∃ q, ∀ x, f(x) = (x - a) * q(x) を取り出す。
      x := a を代入すると f(a) = (a - a) * q(a)。
      ring_add_neg_r より a - a = 0、ring_mul_zero_l より 0 * q(a) = 0。  *)
Lemma poly_root_of_factor :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_divides_linear F f a ->
    poly_eval F f a = ring_zero F.
Proof.
  intros F f a [q Hq].
  rewrite (Hq a).
  rewrite ring_add_neg_r.
  apply ring_mul_zero_l.
Qed.

(** 主定理: 体上の多項式の因数定理
    任意の体 F 上の多項式 f と元 a に対して次は同値:
      (1) f(x) が (x - a) で割り切れる  (poly_divides_linear F f a)
      (2) f(a) = 0
      (3) a が f(x) = 0 の解
    (2) と (3) は同じ命題。(1) ↔ (2) を示す。

    証明の方針:
      → は poly_root_of_factor、← は poly_factor_of_root を使う。  *)
Theorem factor_theorem :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_divides_linear F f a <-> poly_eval F f a = ring_zero F.
Proof.
  intros F f a.
  split.
  - apply poly_root_of_factor.
  - apply poly_factor_of_root.
Qed.

(** 系: Fp 上の多項式の因数定理
    素数 p のとき Fp = Z/pZ 上の多項式 f と元 a に対して次は同値:
      (1) f(x) が (x - a) で割り切れる
      (2) f(a) = 0
      (3) a が f(x) = 0 の解

    証明の方針: factor_theorem を znz_p_field p Hp に適用。  *)
Corollary fp_factor_theorem :
  forall (p : nat) (Hp : prime (Z.of_nat p))
         (f : list (ring_carrier (znz_p_field p Hp)))
         (a : ring_carrier (znz_p_field p Hp)),
    poly_divides_linear (znz_p_field p Hp) f a <->
    poly_eval (znz_p_field p Hp) f a = ring_zero (znz_p_field p Hp).
Proof.
  intros p Hp f a.
  apply factor_theorem.
Qed.

(** ============================================================
    体上の多項式の根の個数の上界 (Roots Bound for Polynomials over a Field)
    ============================================================

    主定理: 体 F 上の先頭係数非零の多項式 f (長さ n+1, すなわち n 次多項式) の
    の n 個である。

    証明の概略:
      length f に関する強帰納法。
      - 定数 (長さ 1): 先頭係数非零ならば根がない。
      - 長さ n+1 (n ≥ 1): 根 a を一つ取り、因数定理よ
          f(x) = (x - a) * q(x)  (q = poly_synthetic_div F f a)
        と分解する。q の長さは n, 先頭係数も非零。
        残りの根 rest は  length rest < n。の根であり、帰先頭係数も非零。先頭係数も非零。
        よって length (a :: rest) ≤ n < n + 1 = length f。  *)

(** 定義: 先頭係数非零の多項式
    多項式 f が空でなく、かつ最高次係数 (last 要素) が非零であることを表す。  *)
Definition poly_nonzero_leading (F : Field) (f : list (ring_carrier F)) : Prop :=
  f <> [] /\ last f (ring_zero F) <> ring_zero F.

(** 補題: 合成除算後も先頭係数非零が保たれる
    poly_nonzero_leading F f かつ length f ≥ 2 ならば
    poly_nonzero_leading F (poly_synthetic_div F f a)

    証明の方針:
      - 空でないことは poly_synthetic_div_length から示す。
      - 先頭係数の保存は poly_synthetic_div_last から示す。  *)
Lemma poly_nonzero_leading_div :
  forall (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F),
    poly_nonzero_leading F f ->
    (2 <= length f)%nat ->
    poly_nonzero_leading F (poly_synthetic_div F f a).
Proof.
  intros F f a [Hne Hlast] Hlen.
  split.
  - (* poly_synthetic_div F f a ≠ [] *)
    intro Hempty.
    destruct f as [| c cs]. { contradiction. }
    pose proof (poly_synthetic_div_length F c cs a) as Hk.
    rewrite Hempty in Hk. simpl in Hk.
    simpl in Hlen. lia.
  - (* last (poly_synthetic_div F f a) (ring_zero F) ≠ ring_zero F *)
    rewrite poly_synthetic_div_last by exact Hlen.
    exact Hlast.
Qed.

(** 補題: 非零定数多項式は根を持たない
    c ≠ ring_zero F ならば poly_eval F [c] x ≠ ring_zero F

    証明の方針: poly_eval_single で rewrite して仮定と同じ形にする。  *)
Lemma poly_const_nonzero_no_root :
  forall (F : Field) (c x : ring_carrier F),
    c <> ring_zero F ->
    poly_eval F [c] x <> ring_zero F.
Proof.
  intros F c x Hc.
  rewrite poly_eval_single.
  exact Hc.
Qed.

(** 補題: 異なる根の分離
    f(a) = 0, f(b) = 0, b ≠ a ならば (poly_synthetic_div F f a)(b) = 0

: 1775132645:1;rocq compile integer.v
      1. poly_remainder_theorem: f(b) = (b - a) * q(b) + f(a) より
            ring_zero F = (b - a) * q(b) を得る (f(a)=0, f(b)=0 を代入)。
      2. b ≠ a ⟹ ring_sub_zero_iff_eq の対偶より b - a ≠ 0。
      3. field_no_zero_divisors: (b-a)*q(b) = 0 ∧ b-a ≠ 0 ⟹ q(b) = 0。  *)
Lemma poly_div_root :
  forall (F : Field) (f : list (ring_carrier F)) (a b : ring_carrier F),
    poly_eval F f a = ring_zero F ->
    poly_eval F f b = ring_zero F ->
    b <> a ->
    poly_eval F (poly_synthetic_div F f a) b = ring_zero F.
Proof.
  intros F f a b Ha Hb Hne.
  pose proof (poly_remainder_theorem F f a b) as Hremainder.
  rewrite Hb, Ha, ring_add_zero_r in Hremainder.
  symmetry in Hremainder.
  apply field_no_zero_divisors in Hremainder.
  destruct Hremainder as [Habs | Hq].
  - exfalso. apply Hne. apply ring_sub_zero_iff_eq. exact Habs.
  - exact Hq.
Qed.

(** 主定理: 体上の多項式の根の個数の上界
    体 F 上の先頭係数非零の多項式 f に対して、
    f(a) = 0 を満たす互いに相異なる元のリスト roots が存在するとき、
      length roots < length f
    が成り立つ。言い換えれば f の根はたかだか (length f - 1) = (次 個。

    証明の方針: length f の値 n に関する帰納法 (≤ 版強帰納法)。
      n = 0: f = [] で poly_nonzero_leading の前提に矛盾。
      n = S n': f = c :: cs とする。
        roots = []: 0 < length f なので自明。
        roots = a :: rest:
          a が f の根 ⟹ f = (x-a)*q (因数定理), q = poly_synthetic_div F f a。
          cs = [] (f が定数) のとき: c = f(a) = 0 で Hlast に矛盾。
          cs = c' :: cs' のとき:
            poly_nonzero_leading F q (poly_nonzero_leading_div)
            rest の各元は q の根 (poly_div_root)
            IH より length rest < length q = length cs
            ∴ length (a :: rest) = 1 + length rest < 1 + length cs = length f ✓  *)
Theorem poly_roots_bound :
  forall (F : Field) (f : list (ring_carrier F)),
    poly_nonzero_leading F f ->
    forall (roots : list (ring_carrier F)),
      NoDup roots ->
      (forall a, In a roots -> poly_eval F f a = ring_zero F) ->
      (length roots < length f)%nat.
Proof.
  intros F.
  assert (Hmain : forall n (f : list (ring_carrier F)),
    (length f <= n)%nat ->
    poly_nonzero_leading F f ->
    forall (roots : list (ring_carrier F)),
      NoDup roots ->
      (forall a, In a roots -> poly_eval F f a = ring_zero F) ->
      (length roots < length f)%nat).
  2: { intros f Hpnl. exact (Hmain (length f) f (le_n _) Hpnl). }
  intros n.
  induction n as [| n' IHn]; intros f Hlen [Hne Hlast] roots Hnd Hroots.
  - (* n = 0: length f = 0, f ≠ [] に矛盾 *)
    destruct f.
    + contradiction.
    + simpl in Hlen. lia.
  - (* n = S n': length f ≤ S n' *)
    destruct f as [| c cs].
    { contradiction. }
    destruct roots as [| a rest].
    + (* roots = [] *)
      simpl. lia.
    + (* roots = a :: rest *)
      assert (Ha : poly_eval F (c :: cs) a = ring_zero F).
      { apply Hroots. left. reflexivity. }
      set (q := poly_synthetic_div F (c :: cs) a).
      assert (Hlq : length q = length cs).
      { unfold q. apply poly_synthetic_div_length. }
      assert (Hlen_cs : (length cs <= n')%nat) by (simpl in Hlen; lia).
      assert (Hlq_le : (length q <= n')%nat) by lia.
      destruct cs as [| c' cs'].
      * (* cs = [], f = [c]: c ≠ 0 だが f(a) = 0 なので矛盾 *)
        exfalso. apply Hlast.
        simpl.
        rewrite <- (poly_eval_single F c a). exact Ha.
      * (* cs = c' :: cs', length f ≥ 2 *)
        assert (Hpnl_q : poly_nonzero_leading F q).
        { apply poly_nonzero_leading_div.
          - split; [discriminate | exact Hlast].
          - simpl. lia. }
        assert (Hnd_rest : NoDup rest).
        { inversion Hnd; assumption. }
        assert (Hnotin : ~ In a rest).
        { inversion Hnd; assumption. }
        assert (Hroots_q : forall b, In b rest -> poly_eval F q b = ring_zero F).
        { intros b Hb.
          unfold q.
          apply (poly_div_root F (c :: c' :: cs') a b Ha).
          - apply Hroots. right. exact Hb.
          - intros Heq. subst b. exact (Hnotin Hb). }
        assert (Hlen_rest : (length rest < length q)%nat).
        { exact (IHn q Hlq_le Hpnl_q rest Hnd_rest Hroots_q). }
        rewrite Hlq in Hlen_rest.
        simpl length in Hlen_rest.
        simpl length.
        lia.
Qed.

(** 系: Fp 上の多項式の根の個数の上界
: 1775132645:1;rocq compile integer.v (次数) 個。

    証明の方針: poly_roots_bound を znz_p_field p Hp に適用。  *)
Corollary fp_poly_roots_bound :
  forall (p : nat) (Hp : prime (Z.of_nat p))
         (f : list (ring_carrier (znz_p_field p Hp))),
    poly_nonzero_leading (znz_p_field p Hp) f ->
    forall (roots : list (ring_carrier (znz_p_field p Hp))),
      NoDup roots ->
      (forall a, In a roots ->
        poly_eval (znz_p_field p Hp) f a =
        ring_zero (znz_p_field p Hp)) ->
      (length roots < length f)%nat.
Proof.
  intros p Hp f Hpnl roots Hnd Hroots.
  apply poly_roots_bound; assumption.
Qed.

(** ===================================================================== *)
(** 元の位数 (Element Order in a Finite Group)                            *)
(**                                                                        *)
(** 有限群 G において、元 a の位数 (element order) とは                   *)
(**   ord(a) = min { d ∈ ℕ | d > 0 ∧ a^d = e }                          *)
(**                                                                        *)
(** 主定理:                                                                *)
(**   (1) a^0, a^1, ..., a^(ord(a)-1) はすべて異なる                     *)
(**   (2) a^x = e ⟺ ord(a) | x                                           *)
(**                                                                        *)
(** さらに素数 p に対して (Z/pZ)* の乗法位数 mult_order_p を定義し、     *)
(** 定理 (1)(2) の系として乗法位数の性質を形式化する。                   *)
(** ===================================================================== *)

(** フェーズ1: 有限群の元は有限の周期を持つ

    GroupOrder G m （位数 m の有限群）のとき、任意の元 a は
    正の自然数 d ≤ m で a^d = e となるものが存在する。

    証明の方針:
      GroupOrder G m から単射 f : carrier G → Fin.t m を取り出す。
      写像 h(k) := f(a^k) を鳩ノ巣原理 (pigeonhole_Fin) に適用すると
      i < j ≤ m かつ f(a^i) = f(a^j) となる i, j が存在する。
      f の単射性から a^i = a^j (自然数冪)。
      equal_powers_imply_period から a^(j-i) = e が得られる。
      d = j - i > 0 が求める周期である。  *)
Lemma element_has_finite_period :
  forall (G : Group) (m : nat) (a : carrier G),
    (0 < m)%nat ->
    GroupOrder G m ->
    exists d : nat, (0 < d)%nat /\ gpow G a (Z.of_nat d) = e G.
Proof.
  intros G m a Hm Hord.
  destruct Hord as [f [Hinj Hsurj]].
  destruct (pigeonhole_Fin m (fun k => f (gpow_nat G a k)))
    as [i [j [Hij [Hjm Heq]]]].
  assert (Hpow : gpow_nat G a i = gpow_nat G a j).
  { apply Hinj. exact Heq. }
  exists (j - i)%nat.
  split.
  - lia.
  - apply equal_powers_imply_period.
    + exact Hij.
    + rewrite !gpow_of_nat. exact Hpow.
Qed.

(** 最小周期の存在:
    有限群 G の元 a に対して、正の周期の集合は空でない。
    整列原理 (well_ordering_nat) を適用すると最小の正の周期 d が存在する。
    この d が元の位数の候補となる。

    証明の方針:
      element_has_finite_period で存在を示す。
      well_ordering_nat に述語 P d := (0 < d) ∧ (a^d = e) を渡す。
      最小元 d を得て、それが minimality 条件も満たすことを示す。  *)
Lemma mult_order_exists :
  forall (G : Group) (m : nat) (Hm : GroupOrder G m) (a : carrier G),
    exists d : nat,
      (0 < d)%nat /\
      gpow G a (Z.of_nat d) = e G /\
      forall d' : nat,
        (0 < d')%nat -> gpow G a (Z.of_nat d') = e G -> (d <= d')%nat.
Proof.
  intros G m Hm a.
  pose proof (group_order_pos G m Hm) as Hm_pos.
  pose proof (element_has_finite_period G m a Hm_pos Hm) as [d0 [Hd0_pos Hd0_e]].
  set (P := fun d => (0 < d)%nat /\ gpow G a (Z.of_nat d) = e G).
  assert (HP : exists n, P n) by (exists d0; split; assumption).
  destruct (well_ordering_nat P HP) as [d [HPd Hmin]].
  destruct HPd as [Hd_pos Hd_e].
  exists d.
  split. { exact Hd_pos. }
  split. { exact Hd_e. }
  intros d' Hd'_pos Hd'_e.
  destruct (classic (d' < d)%nat) as [Hlt | Hnlt].
  - exfalso. exact (Hmin d' Hlt (conj Hd'_pos Hd'_e)).
  - lia.
Qed.

(** 元の位数の定義 (Element Order):
    有限群 G の元 a に対して、元の位数 mult_order G m Hm a を
    「最小の正の周期 d」として epsilon（古典論理の選択関数）で定義する。

    epsilon の仕様: epsilon spec P = v s.t. P v ならば P (epsilon spec P)

    mult_order_exists が「最小周期を満たす値が存在する」ことを保証する。
    epsilon_spec を使って mult_order_spec でその仕様を証明する。  *)
Definition mult_order (G : Group) (m : nat) (Hm : GroupOrder G m)
    (a : carrier G) : nat :=
  epsilon (inhabits 0%nat) (fun d =>
    (0 < d)%nat /\
    gpow G a (Z.of_nat d) = e G /\
    forall d' : nat,
      (0 < d')%nat -> gpow G a (Z.of_nat d') = e G -> (d <= d')%nat).

(** 元の位数の仕様:
    mult_order G m Hm a は以下を満たす:
      (1) mult_order G m Hm a > 0（正）
      (2) a^(mult_order G m Hm a) = e（単位元に戻る）
      (3) 最小性: 他の正の周期 d' に対して mult_order ≤ d'

    証明の方針: epsilon_spec と mult_order_exists を組み合わせる。  *)
Lemma mult_order_spec :
  forall (G : Group) (m : nat) (Hm : GroupOrder G m) (a : carrier G),
    let d := mult_order G m Hm a in
    (0 < d)%nat /\
    gpow G a (Z.of_nat d) = e G /\
    forall d' : nat,
      (0 < d')%nat -> gpow G a (Z.of_nat d') = e G -> (d <= d')%nat.
Proof.
  intros G m Hm a.
  unfold mult_order.
  apply epsilon_spec.
  exact (mult_order_exists G m Hm a).
Qed.

(** フェーズ2: 元の位数の主要性質 *)

(** 周期キャンセル補題:
    a^d = e ならば a^(d*k + r) = a^r

    証明の方針:
      gpow_nat_add で a^(d*k+r) = a^(d*k) * a^r に分解。
      gpow_nat_mul で a^(d*k) = (a^d)^k に変換。
      a^d = e（仮定 Hd）を代入して e^k = e（gpow_nat_e）。
      e * a^r = a^r（id_left）。  *)
Lemma gpow_nat_period_cancel :
  forall (G : Group) (a : carrier G) (d k r : nat),
    gpow_nat G a d = e G ->
    gpow_nat G a (d * k + r) = gpow_nat G a r.
Proof.
  intros G a d k r Hd.
  rewrite gpow_nat_add.
  rewrite gpow_nat_mul.
  rewrite Hd.
  rewrite gpow_nat_e.
  apply id_left.
Qed.

(** 定理2: a^x = e ⟺ ord(a) | x

    有限群 G の元 a とその位数 d = mult_order G m Hm a に対して、
      gpow_nat G a x = e G  ⟺  (d | x)%nat
    が成り立つ。

    証明の方針:
    ← 方向: x = d * k のとき、gpow_nat_period_cancel（r=0）から a^x = a^0 = e。
    → 方向: x = d*(x/d) + (x mod d) と書いて gpow_nat_period_cancel を適用。
      a^(x mod d) = e が得られる。
      もし x mod d > 0 なら 0 < x mod d < d で a^(x mod d) = e、最小性に矛盾。
      よって x mod d = 0、すなわち d | x。  *)
Theorem mult_order_divides :
  forall (G : Group) (m : nat) (Hm : GroupOrder G m)
         (a : carrier G) (x : nat),
    gpow_nat G a x = e G <-> Nat.divide (mult_order G m Hm a) x.
Proof.
  intros G m Hm a x.
  pose proof (mult_order_spec G m Hm a) as [Hord_pos [Hord_e Hord_min]].
  set (d := mult_order G m Hm a).
  assert (Hd_nat : gpow_nat G a d = e G).
  { rewrite <- gpow_of_nat. exact Hord_e. }
  split.
  - (* → 方向: a^x = e → d | x *)
    intros Hx.
    set (q := (x / d)%nat).
    set (r := (x mod d)%nat).
    assert (Hdiv : (x = d * q + r)%nat).
    { unfold q, r. pose proof (Nat.div_mod x d ltac:(lia)). lia. }
    assert (Hr_lt : (r < d)%nat).
    { unfold r. apply Nat.mod_upper_bound. lia. }
    assert (Hcancel : gpow_nat G a (d * q + r) = gpow_nat G a r).
    { apply gpow_nat_period_cancel. exact Hd_nat. }
    assert (Har_e : gpow_nat G a r = e G).
    { rewrite <- Hcancel. rewrite <- Hdiv. exact Hx. }
    destruct (Nat.eq_dec r 0) as [Hr0 | Hr_ne].
    + exists q. rewrite Nat.mul_comm. lia.
    + exfalso.
      assert (Hrpos : (0 < r)%nat) by lia.
      assert (Hle : (d <= r)%nat).
      { apply Hord_min.
        - exact Hrpos.
        - rewrite gpow_of_nat. exact Har_e. }
      lia.
  - (* ← 方向: Nat.divide d x → a^x = e *)
    intros [k Hk].
    rewrite Hk.
    rewrite Nat.mul_comm.
    rewrite gpow_nat_mul.
    rewrite Hd_nat.
    apply gpow_nat_e.
Qed.

(** 定理1: a^0, ..., a^(ord-1) はすべて異なる

    有限群 G の元 a とその位数 d = mult_order G m Hm a に対して、
    0 ≤ i, j < d かつ i ≠ j ならば a^i ≠ a^j。

    証明の方針:
      対称性より i < j の場合のみ示せばよい。
      a^i = a^j を仮定すると equal_powers_imply_period から a^(j-i) = e。
      0 < j-i < d なので最小性（mult_order_spec）に矛盾。  *)
Theorem mult_order_powers_distinct :
  forall (G : Group) (m : nat) (Hm : GroupOrder G m)
         (a : carrier G) (i j : nat),
    (i < mult_order G m Hm a)%nat ->
    (j < mult_order G m Hm a)%nat ->
    i <> j ->
    gpow_nat G a i <> gpow_nat G a j.
Proof.
  intros G m Hm a i j Hi Hj Hne Heq.
  set (d := mult_order G m Hm a).
  pose proof (mult_order_spec G m Hm a) as [Hd_pos [Hd_e Hd_min]].
  destruct (classic (i < j)%nat) as [Hij | Hji].
  - (* i < j の場合 *)
    assert (Hperiod : gpow G a (Z.of_nat (j - i)) = e G).
    { apply equal_powers_imply_period.
      - exact Hij.
      - rewrite !gpow_of_nat. exact Heq. }
    assert (Hpos : (0 < j - i)%nat) by lia.
    assert (Hlt  : (j - i < d)%nat) by lia.
    pose proof (Hd_min (j - i)%nat Hpos Hperiod) as Hle.
    lia.
  - (* j < i の場合 *)
    assert (Hji' : (j < i)%nat) by lia.
    assert (Hperiod : gpow G a (Z.of_nat (i - j)) = e G).
    { apply equal_powers_imply_period.
      - exact Hji'.
      - rewrite !gpow_of_nat. exact (eq_sym Heq). }
    assert (Hpos : (0 < i - j)%nat) by lia.
    assert (Hlt  : (i - j < d)%nat) by lia.
    pose proof (Hd_min (i - j)%nat Hpos Hperiod) as Hle.
    lia.
Qed.

(** フェーズ3: (Z/pZ)* への適用 (Multiplicative Order mod p) *)

(** euler_phi p = p - 1 for prime p

    証明の方針:
      euler_phi_prime_pow を e=1 で適用:
        euler_phi (p^1) = p^(1-1) * (p-1) = p^0 * (p-1) = 1 * (p-1) = p-1
      Nat.pow_1_r で p^1 = p を得て rewrite する。  *)
Lemma euler_phi_prime :
  forall (p : nat),
    prime (Z.of_nat p) ->
    euler_phi p = (p - 1)%nat.
Proof.
  intros p Hp.
  pose proof (euler_phi_prime_pow p 1 Hp (Nat.le_refl 1)) as H.
  rewrite Nat.pow_1_r in H.
  simpl in H.
  lia.
Qed.

(** (Z/pZ)* の群位数は p-1 (for prime p)

    証明の方針:
      euler_phi_group_order: GroupOrder (znz_units_group p Hp) (euler_phi p)
      euler_phi_prime: euler_phi p = p-1
      を組み合わせる。  *)
Lemma prime_units_group_order :
  forall (p : nat) (Hp : (1 < p)%nat),
    prime (Z.of_nat p) ->
    GroupOrder (znz_units_group p Hp) (p - 1).
Proof.
  intros p Hp Hprime.
  pose proof (euler_phi_group_order p Hp) as H.
  rewrite euler_phi_prime in H by exact Hprime.
  exact H.
Qed.

(** 乗法位数 (Multiplicative Order mod p) の定義:
    素数 p と a ∈ (Z/pZ)* に対して、乗法位数 mult_order_p p Hp Hprime a を
    一般群の元の位数 mult_order を (Z/pZ)* に適用して定義する。  *)
Definition mult_order_p (p : nat) (Hp : (1 < p)%nat)
    (Hprime : prime (Z.of_nat p))
    (a : carrier (znz_units_group p Hp)) : nat :=
  mult_order (znz_units_group p Hp) (p - 1)
             (prime_units_group_order p Hp Hprime) a.

(** (Z/pZ)* における定理1の系:
    a^0, a^1, ..., a^(ord_p(a)-1) はすべて異なる

    証明の方針: mult_order_powers_distinct を znz_units_group に特化。  *)
Corollary mult_order_p_powers_distinct :
  forall (p : nat) (Hp : (1 < p)%nat)
         (Hprime : prime (Z.of_nat p))
         (a : carrier (znz_units_group p Hp))
         (i j : nat),
    (i < mult_order_p p Hp Hprime a)%nat ->
    (j < mult_order_p p Hp Hprime a)%nat ->
    i <> j ->
    gpow_nat (znz_units_group p Hp) a i <>
    gpow_nat (znz_units_group p Hp) a j.
Proof.
  intros p Hp Hprime a i j Hi Hj Hne.
  unfold mult_order_p in *.
  exact (mult_order_powers_distinct (znz_units_group p Hp) (p - 1)
           (prime_units_group_order p Hp Hprime) a i j Hi Hj Hne).
Qed.

(** (Z/pZ)* における定理2の系:
    a^x ≡ 1 (mod p) ⟺ ord_p(a) | x

    証明の方針: mult_order_divides を znz_units_group に特化。  *)
Corollary mult_order_p_divides :
  forall (p : nat) (Hp : (1 < p)%nat)
         (Hprime : prime (Z.of_nat p))
         (a : carrier (znz_units_group p Hp))
         (x : nat),
    gpow_nat (znz_units_group p Hp) a x =
      e (znz_units_group p Hp)
    <->
    Nat.divide (mult_order_p p Hp Hprime a) x.
Proof.
  intros p Hp Hprime a x.
  unfold mult_order_p.
  exact (mult_order_divides (znz_units_group p Hp) (p - 1)
           (prime_units_group_order p Hp Hprime) a x).
Qed.

(** ===================================================================== *)
(** 原始根の存在定理のための補題群                                        *)
(** (Auxiliary Lemmas for Primitive Root Existence)                        *)
(** ===================================================================== *)

(** 右消去法則 (Right Cancellation):
    a * z = b * z ならば a = b.
    証明: 両辺に右から z の逆元を掛け、結合律・逆元・単位元を適用する。 *)
Lemma op_cancel_r : forall (G : Group) (x y z : carrier G),
  op G x z = op G y z -> x = y.
Proof.
  intros G x y z H.
  assert (Hstep : op G (op G x z) (inv G z) = op G (op G y z) (inv G z)).
  { rewrite H. reflexivity. }
  rewrite <- (assoc G x z (inv G z)), <- (assoc G y z (inv G z)) in Hstep.
  rewrite !inv_right, !id_right in Hstep.
  exact Hstep.
Qed.

(** 全群要素のリスト (List of All Group Elements):
    GroupOrder G n をもつ群の全元を NoDup リストとして取り出す。
    全単射 f : carrier G → Fin.t n の逆像を epsilon で構成し、
    fin_all n の像として全元リストを得る。 *)
Lemma group_elements_list :
  forall (G : Group) (n : nat) (Hn : GroupOrder G n),
    exists L : list (carrier G),
      List.NoDup L /\ length L = n /\ forall x : carrier G, List.In x L.
Proof.
  intros G n [f [Hinj Hsurj]].
  set (g := fun (i : Fin.t n) =>
    epsilon (inhabits (e G)) (fun x : carrier G => f x = i)).
  assert (Hg : forall i : Fin.t n, f (g i) = i).
  { intro i. apply epsilon_spec. exact (Hsurj i). }
  exists (List.map g (fin_all n)).
  split.
  - (* NoDup: g は単射 *)
    apply List.NoDup_map_NoDup_ForallPairs.
    + intros a b _ _ Heq.
      assert (Hfab : f (g a) = f (g b)) by (rewrite Heq; reflexivity).
      rewrite (Hg a), (Hg b) in Hfab. exact Hfab.
    + apply fin_all_NoDup.
  - split.
    + (* length = n *)
      rewrite List.map_length, fin_all_length. reflexivity.
    + (* 全射: 任意の x が含まれる *)
      intros x.
      assert (Hfx_in : List.In (f x) (fin_all n)) by apply fin_all_complete.
      assert (Hin : List.In (g (f x)) (List.map g (fin_all n))).
      { apply List.in_map. exact Hfx_in. }
      assert (Hgfx : g (f x) = x).
      { apply Hinj. rewrite Hg. reflexivity. }
      rewrite Hgfx in Hin. exact Hin.
Qed.

(** (Z/pZ)* の演算は可換 (Commutativity of znz_units_group):
    乗法 mod p は Z の乗法から Z.mul_comm で可換性を得る。 *)
Lemma znz_units_op_comm :
  forall (p : nat) (Hp : (1 < p)%nat)
         (a b : carrier (znz_units_group p Hp)),
    op (znz_units_group p Hp) a b = op (znz_units_group p Hp) b a.
Proof.
  intros p Hp a b.
  apply sig_eq. simpl.
  rewrite Z.mul_comm. reflexivity.
Qed.

(** 可換群での左乗算の fold_right への影響:
    fold_right (op G) e (map (fun x => op G a x) L) = a^(length L) * fold_right (op G) e L.
    証明: L についての帰納法。再帰ステップは可換律 G_abelian を使って
      (a*x)*(a^n*P) = (a*a^n)*(x*P) を rewrite で変形する。 *)
Lemma fold_right_mul_left_abelian :
  forall (G : Group)
         (G_abelian : forall a b : carrier G, op G a b = op G b a)
         (a : carrier G) (L : list (carrier G)),
    fold_right (op G) (e G) (List.map (fun x => op G a x) L) =
    op G (gpow_nat G a (length L)) (fold_right (op G) (e G) L).
Proof.
  intros G G_abelian a L.
  induction L as [| x L' IH].
  - (* Base: L = [] *)
    simpl. rewrite id_left. reflexivity.
  - (* Step: L = x :: L' *)
    simpl.
    rewrite IH.
    set (an := gpow_nat G a (length L')).
    set (P := fold_right (op G) (e G) L').
    (* Goal: (a*x)*(an*P) = (a*an)*(x*P) *)
    rewrite <- (assoc G a x (op G an P)).
    rewrite (assoc G x an P).
    rewrite (G_abelian x an).
    rewrite <- (assoc G an x P).
    rewrite (assoc G a an (op G x P)).
    reflexivity.
Qed.

(** 左乗算は全元リストの置換を与える (Left Multiplication Permutes Elements):
    NoDup L かつ L が全要素を含むとき、map (op a) L は L の置換。
    証明: NoDup_Permutation を使い、
      - NoDup (map (op a) L): op_cancel_l の単射性から
      - ∀z, In z L ↔ In z (map (op a) L): 逆元 a^{-1} の存在から *)
Lemma znz_units_mul_left_permutation :
  forall (p : nat) (Hp : (1 < p)%nat)
         (a : carrier (znz_units_group p Hp))
         (L : list (carrier (znz_units_group p Hp))),
    List.NoDup L ->
    (forall x : carrier (znz_units_group p Hp), List.In x L) ->
    Permutation L (List.map (fun x => op (znz_units_group p Hp) a x) L).
Proof.
  intros p Hp a L HND Hall.
  set (G := znz_units_group p Hp).
  apply NoDup_Permutation.
  - exact HND.
  - (* NoDup (map (op a) L) *)
    apply List.NoDup_map_NoDup_ForallPairs.
    + intros x y _ _ H.
      exact (op_cancel_l G a x y H).
    + exact HND.
  - intro z.
    split.
    + (* z ∈ L → z ∈ map (op a) L *)
      intro Hz.
      apply List.in_map_iff.
      set (w := op G (inv G a) z).
      exists w.
      split.
      * (* op a (inv a z) = z *)
        unfold w.
        rewrite (assoc G a (inv G a) z), inv_right, id_left.
        reflexivity.
      * apply Hall.
    + (* z ∈ map (op a) L → z ∈ L *)
      intro Hz.
      apply List.in_map_iff in Hz.
      destruct Hz as [w [Haw Hw]].
      rewrite <- Haw. apply Hall.
Qed.

(** Permutation 下での fold_right 不変性 (可換群):
    G がアーベル群で Permutation L L' ならば fold_right の値が等しい。
    証明: Permutation の帰納的構造に従い、
      perm_swap で x*(y*P) = y*(x*P) を交換律から示す。 *)
Lemma fold_right_permutation_abelian :
  forall (G : Group)
         (G_abelian : forall a b : carrier G, op G a b = op G b a)
         (L L' : list (carrier G)),
    Permutation L L' ->
    fold_right (op G) (e G) L = fold_right (op G) (e G) L'.
Proof.
  intros G G_abelian L L' HP.
  induction HP as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2].
  - (* perm_nil *)
    reflexivity.
  - (* perm_skip: x :: l → x :: l' *)
    simpl. rewrite IH. reflexivity.
  - (* perm_swap: y :: x :: l → x :: y :: l *)
    simpl.
    set (P := fold_right (op G) (e G) l).
    (* Goal: op G y (op G x P) = op G x (op G y P) *)
    rewrite (assoc G y x P), (G_abelian y x), <- (assoc G x y P).
    reflexivity.
  - (* perm_trans *)
    rewrite IH1, IH2. reflexivity.
Qed.

(** フェルマーの小定理 (Fermat's Little Theorem):
    素数 p に対して、(Z/pZ)* の任意の元 a は a^(p-1) = 1 を満たす。

    証明の方針:
      1. (Z/pZ)* の全要素リスト L を取り出す（group_elements_list）。
      2. 左乗算 x ↦ a*x は L の置換（znz_units_mul_left_permutation）。
      3. 置換不変性より fold_right (op) e L = fold_right (op) e (map (op a) L)。
      4. fold_right_mul_left_abelian より
           fold_right (op) e (map (op a) L) = a^(p-1) * fold_right (op) e L。
      5. P = fold_right (op) e L として P = a^(p-1) * P。
      6. 右消去法則 op_cancel_r より a^(p-1) = e。 *)
Lemma fermat_little_theorem :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (a : carrier (znz_units_group p Hp)),
    gpow_nat (znz_units_group p Hp) a (p - 1) = e (znz_units_group p Hp).
Proof.
  intros p Hp Hprime a.
  set (G := znz_units_group p Hp).
  assert (Hord : GroupOrder G (p - 1)) by exact (prime_units_group_order p Hp Hprime).
  destruct (group_elements_list G (p - 1) Hord) as [L [HND [Hlen Hall]]].
  set (P := fold_right (op G) (e G) L).
  (* 置換: L と map (op a) L *)
  assert (Hperm : Permutation L (List.map (fun x => op G a x) L)).
  { apply znz_units_mul_left_permutation; assumption. }
  (* 置換不変性: fold L = fold (map (op a) L) *)
  assert (Hfeq : fold_right (op G) (e G) L =
                 fold_right (op G) (e G) (List.map (fun x => op G a x) L)).
  { apply fold_right_permutation_abelian.
    - exact (znz_units_op_comm p Hp).
    - exact Hperm. }
  (* fold (map (op a) L) = a^(p-1) * P *)
  assert (Hmul : fold_right (op G) (e G) (List.map (fun x => op G a x) L) =
                 op G (gpow_nat G a (p - 1)) P).
  { unfold P. rewrite <- Hlen.
    exact (fold_right_mul_left_abelian G (znz_units_op_comm p Hp) a L). }
  (* P = a^(p-1) * P *)
  assert (HP : P = op G (gpow_nat G a (p - 1)) P).
  { unfold P at 1. exact (eq_trans Hfeq Hmul). }
  (* 右消去: a^(p-1) = e *)
  apply (op_cancel_r G (gpow_nat G a (p - 1)) (e G) P).
  rewrite id_left.
  exact (eq_sym HP).
Qed.

(** 乗法位数は p-1 を割り切る (Multiplicative Order Divides p-1):
    フェルマーの小定理 a^(p-1) = 1 と mult_order_p_divides の組み合わせ。 *)
Lemma mult_order_p_divides_p_minus_1 :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (a : carrier (znz_units_group p Hp)),
    Nat.divide (mult_order_p p Hp Hprime a) (p - 1).
Proof.
  intros p Hp Hprime a.
  apply (proj1 (mult_order_p_divides p Hp Hprime a (p - 1))).
  exact (fermat_little_theorem p Hp Hprime a).
Qed.
(** ===================================================================== *)
(** 原始根の存在定理: フェーズ 2                                          *)
(** (Z/pZ)* から体 Z/pZ への埋め込みと多項式の根の解析                   *)
(** ===================================================================== *)

(** (Z/pZ)* の元を体 Z/pZ に埋め込む埋め込み写像。
    台集合 {x : Z | 0≤x<p ∧ gcd(x,p)=1} から {x : Z | 0≤x<p} への自然な射影。 *)
Definition znz_units_to_field (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
    (x : carrier (znz_units_group p Hp)) : ring_carrier (znz_p_field p Hprime) :=
  exist _ (proj1_sig x) (proj1 (proj2_sig x)).

(** 埋め込みは乗算と可換: embed(a * b) = embed(a) * embed(b)。
    両者が同じ mod 計算に帰着するので sig_eq で示す。 *)
Lemma znz_units_to_field_mul :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (x y : carrier (znz_units_group p Hp)),
    ring_mul (znz_p_field p Hprime)
      (znz_units_to_field p Hp Hprime x)
      (znz_units_to_field p Hp Hprime y) =
    znz_units_to_field p Hp Hprime (op (znz_units_group p Hp) x y).
Proof.
  intros p Hp Hprime x y. apply sig_eq. simpl. reflexivity.
Qed.

(** 埋め込みは単位元を環の 1 に送る。
    e G = exist _ 1 _、ring_one F = exist _ (1 mod p) _、
    p ≥ 2 のとき 1 mod p = 1 なので sig_eq で一致する。 *)
Lemma znz_units_to_field_one :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p)),
    znz_units_to_field p Hp Hprime (e (znz_units_group p Hp)) =
    ring_one (znz_p_field p Hprime).
Proof.
  intros p Hp Hprime. apply sig_eq. simpl.
  symmetry. apply Z.mod_small. apply prime_ge_2 in Hprime. lia.
Qed.

(** 体における n 乗: ring_pow_nat F a 0 = 1、ring_pow_nat F a (n+1) = a * a^n。 *)
Fixpoint ring_pow_nat (F : Field) (a : ring_carrier F) (n : nat) : ring_carrier F :=
  match n with
  | O => ring_one F
  | S n' => ring_mul F a (ring_pow_nat F a n')
  end.

(** 埋め込みは冪を保つ: ring_pow_nat F (embed a) n = embed (gpow_nat G a n)。
    帰納: 底は znz_units_to_field_one、ステップは znz_units_to_field_mul。 *)
Lemma znz_units_to_field_pow :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (x : carrier (znz_units_group p Hp)) (n : nat),
    ring_pow_nat (znz_p_field p Hprime) (znz_units_to_field p Hp Hprime x) n =
    znz_units_to_field p Hp Hprime (gpow_nat (znz_units_group p Hp) x n).
Proof.
  intros p Hp Hprime x n.
  induction n as [| n' IH].
  - simpl. symmetry. apply znz_units_to_field_one.
  - change (ring_mul (znz_p_field p Hprime) (znz_units_to_field p Hp Hprime x)
      (ring_pow_nat (znz_p_field p Hprime) (znz_units_to_field p Hp Hprime x) n') =
    znz_units_to_field p Hp Hprime
      (op (znz_units_group p Hp) x (gpow_nat (znz_units_group p Hp) x n'))).
    rewrite IH. apply znz_units_to_field_mul.
Qed.

(** 埋め込みは単射: embed x = embed y → x = y。
    proj1_sig の等しさから sig_eq で示す。 *)
Lemma znz_units_to_field_inj :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (x y : carrier (znz_units_group p Hp)),
    znz_units_to_field p Hp Hprime x = znz_units_to_field p Hp Hprime y -> x = y.
Proof.
  intros p Hp Hprime x y Heq.
  apply sig_eq.
  change (proj1_sig x = proj1_sig y).
  set (embed := znz_units_to_field p Hp Hprime) in Heq.
  unfold embed in Heq.
  exact (f_equal (fun e : ring_carrier (znz_p_field p Hprime) => proj1_sig e) Heq).
Qed.

(** 多項式 t^n を小端表現 [0; ...; 0; 1] (n 個の 0 の後に 1) で構成する。 *)
Fixpoint xd_poly (F : Field) (n : nat) : list (ring_carrier F) :=
  match n with
  | O => [ring_one F]
  | S n' => ring_zero F :: xd_poly F n'
  end.

(** xd_poly の評価は ring_pow_nat に等しい。
    帰納: 底は ring_mul_zero_r と ring_add_zero_r、ステップは ring_add_zero_l。 *)
Lemma xd_poly_eval :
  forall (F : Field) (n : nat) (x : ring_carrier F),
    poly_eval F (xd_poly F n) x = ring_pow_nat F x n.
Proof.
  intros F n x.
  induction n as [| n' IH].
  - simpl. rewrite ring_mul_zero_r. apply ring_add_zero_r.
  - simpl. rewrite IH. apply ring_add_zero_l.
Qed.

(** xd_poly の長さは n+1。 *)
Lemma xd_poly_length :
  forall (F : Field) (n : nat), length (xd_poly F n) = S n.
Proof.
  intros F n. induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** xd_poly は空でない。 *)
Lemma xd_poly_nonempty :
  forall (F : Field) (n : nat), xd_poly F n <> [].
Proof.
  intros F n. rewrite <- List.length_zero_iff_nil, xd_poly_length. discriminate.
Qed.

(** xd_poly の末尾要素は ring_one F。
    帰納: last (0 :: l) d = last l d (l ≠ []) から IH を適用。 *)
Lemma xd_poly_last :
  forall (F : Field) (n : nat),
    last (xd_poly F n) (ring_zero F) = ring_one F.
Proof.
  intros F n.
  assert (H : xd_poly F n = List.repeat (ring_zero F) n ++ [ring_one F]).
  { induction n as [| n' IH].
    - reflexivity.
    - unfold xd_poly. fold (xd_poly F n'). rewrite IH.
      reflexivity. }
  rewrite H. apply List.last_last.
Qed.

(** 多項式 t^d - 1 の小端表現: [-1; 0; ...; 0; 1] (d ≥ 1 の場合)。 *)
Definition xd_minus_1_poly (F : Field) (d : nat) : list (ring_carrier F) :=
  match d with
  | O => []
  | S d' => ring_neg F (ring_one F) :: xd_poly F d'
  end.

(** xd_minus_1_poly の長さは d+1 (d ≥ 1 の場合)。 *)
Lemma xd_minus_1_poly_length :
  forall (F : Field) (d : nat),
    (0 < d)%nat ->
    length (xd_minus_1_poly F d) = S d.
Proof.
  intros F d Hd. destruct d as [| d'].
  - lia.
  - simpl. rewrite xd_poly_length. reflexivity.
Qed.

(** xd_minus_1_poly の評価: poly_eval F (t^d - 1) x = (-1) + x^d。 *)
Lemma xd_minus_1_poly_eval :
  forall (F : Field) (d : nat) (x : ring_carrier F),
    (0 < d)%nat ->
    poly_eval F (xd_minus_1_poly F d) x =
    ring_add F (ring_neg F (ring_one F)) (ring_pow_nat F x d).
Proof.
  intros F d x Hd. destruct d as [| d'].
  - lia.
  - simpl xd_minus_1_poly. rewrite poly_eval_cons, xd_poly_eval. reflexivity.
Qed.

Lemma last_nonempty_cons : forall (A : Type) (a : A) (l : list A) (d : A),
  l <> nil -> last (a :: l) d = last l d.
Proof.
  intros A a l d Hne.
  destruct l as [| h t].
  - contradiction.
  - reflexivity.
Qed.

Lemma xd_minus_1_poly_nonzero_leading :
  forall (F : Field) (d : nat),
    (0 < d)%nat ->
    poly_nonzero_leading F (xd_minus_1_poly F d).
Proof.
  intros F d Hd. destruct d as [| d'].
  - lia.
  - split.
    + simpl. discriminate.
    + simpl xd_minus_1_poly.
      rewrite last_nonempty_cons by apply xd_poly_nonempty.
      rewrite xd_poly_last. apply field_one_ne_zero.
Qed.

(** mult_order_p の周期性: a^(mult_order_p ... a) = e。
    mult_order_p_divides の ← 方向を ord(a) | ord(a) に適用。 *)
Lemma mult_order_p_pow_is_e :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (a : carrier (znz_units_group p Hp)),
    gpow_nat (znz_units_group p Hp) a (mult_order_p p Hp Hprime a) =
    e (znz_units_group p Hp).
Proof.
  intros p Hp Hprime a.
  apply (proj2 (mult_order_p_divides p Hp Hprime a (mult_order_p p Hp Hprime a))).
  apply Nat.divide_refl.
Qed.

(** x^d = e ならば embed(x) は field の多項式 t^d - 1 の根。
    embed(x)^d = embed(x^d) = embed(e) = ring_one F。
    poly_eval(-1 + x^d) = -1 + 1 = 0。 *)
Lemma gpow_is_field_root :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (x : carrier (znz_units_group p Hp))
         (d : nat) (Hd : (0 < d)%nat)
         (Hxd : gpow_nat (znz_units_group p Hp) x d = e (znz_units_group p Hp)),
    poly_eval (znz_p_field p Hprime)
      (xd_minus_1_poly (znz_p_field p Hprime) d)
      (znz_units_to_field p Hp Hprime x) =
    ring_zero (znz_p_field p Hprime).
Proof.
  intros p Hp Hprime x d Hd Hxd.
  rewrite xd_minus_1_poly_eval; [| exact Hd].
  rewrite znz_units_to_field_pow, Hxd, znz_units_to_field_one.
  apply ring_add_neg_l.
Qed.

(** a^0,...,a^(d-1) を体に埋め込んだリストは NoDup。
    mult_order_p_powers_distinct より a^i ≠ a^j (i ≠ j, i,j < d)、
    znz_units_to_field_inj より埋め込みの単射性で示す。 *)
Lemma NoDup_field_powers :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (a : carrier (znz_units_group p Hp)) (d : nat)
         (Ha : mult_order_p p Hp Hprime a = d),
    List.NoDup
      (List.map
        (fun k => znz_units_to_field p Hp Hprime (gpow_nat (znz_units_group p Hp) a k))
        (List.seq 0 d)).
Proof.
  intros p Hp Hprime a d Ha.
  apply List.NoDup_map_NoDup_ForallPairs.
  - intros i j Hi Hj Heq.
    apply List.in_seq in Hi. apply List.in_seq in Hj.
    apply znz_units_to_field_inj in Heq.
    destruct (Nat.eq_dec i j) as [Heqij | Hneij].
    + exact Heqij.
    + exfalso.
      apply (mult_order_p_powers_distinct p Hp Hprime a i j).
      * rewrite Ha. lia.
      * rewrite Ha. lia.
      * exact Hneij.
      * exact Heq.
  - apply seq_NoDup.
Qed.

(** 位数 d の元 a が存在するとき、x^d = e ならば x は a の冪乗である。
    証明: a^0,...,a^(d-1) と x をあわせた d+1 個が t^d-1 の根になる。
    fp_poly_roots_bound より d+1 < d+1、矛盾。 *)
Lemma order_d_elements_are_powers :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (a : carrier (znz_units_group p Hp))
         (d : nat) (Hd : (0 < d)%nat)
         (Ha : mult_order_p p Hp Hprime a = d)
         (x : carrier (znz_units_group p Hp))
         (Hx : gpow_nat (znz_units_group p Hp) x d = e (znz_units_group p Hp)),
    exists k : nat, (k < d)%nat /\
      gpow_nat (znz_units_group p Hp) a k = x.
Proof.
  intros p Hp Hprime a d Hd Ha x Hx.
  set (G := znz_units_group p Hp).
  set (F := znz_p_field p Hprime).
  destruct (classic (exists k, (k < d)%nat /\ gpow_nat G a k = x)) as [H | H].
  - exact H.
  - exfalso.
    assert (Hnotpow : forall k, (k < d)%nat -> gpow_nat G a k <> x).
    { intros k Hk Heq. apply H. exists k. exact (conj Hk Heq). }
    set (roots :=
      List.map (fun k => znz_units_to_field p Hp Hprime (gpow_nat G a k)) (List.seq 0 d)
      ++ [znz_units_to_field p Hp Hprime x]).
    assert (Hlen : length roots = S d).
    { unfold roots. rewrite List.app_length, List.map_length, List.seq_length.
      simpl. lia. }
    assert (Hnd : List.NoDup roots).
    { unfold roots. apply List.NoDup_app.
      - apply NoDup_field_powers. exact Ha.
      - constructor. intro Hf. exact Hf. constructor.
      - intros y Hy1 Hy2.
        apply List.in_map_iff in Hy1.
        destruct Hy1 as [k [Hk1 Hk2]].
        apply List.in_seq in Hk2.
        simpl in Hy2. destruct Hy2 as [Hy2 | Hy2]; [| exact Hy2].
        apply (Hnotpow k).
        + lia.
        + apply (znz_units_to_field_inj p Hp Hprime). rewrite Hk1. exact (eq_sym Hy2). }
    assert (Hroots : forall r, List.In r roots ->
        poly_eval F (xd_minus_1_poly F d) r = ring_zero F).
    { intros r Hr.
      unfold roots in Hr. apply List.in_app_iff in Hr.
      destruct Hr as [Hr | Hr].
      - apply List.in_map_iff in Hr.
        destruct Hr as [k [Hk1 Hk2]].
        rewrite <- Hk1.
        apply gpow_is_field_root. exact Hd.
        rewrite <- gpow_nat_mul.
        apply (proj2 (mult_order_p_divides p Hp Hprime a (k * d))).
        rewrite Ha. unfold Nat.divide. exists k. lia.
      - simpl in Hr. destruct Hr as [Hr | Hr]; [| contradiction].
        rewrite <- Hr.
        apply gpow_is_field_root. exact Hd. exact Hx. }
    assert (Hbound : (length roots < length (xd_minus_1_poly F d))%nat).
    { apply fp_poly_roots_bound.
      - apply xd_minus_1_poly_nonzero_leading. exact Hd.
      - exact Hnd.
      - exact Hroots. }
    rewrite Hlen, (xd_minus_1_poly_length F d Hd) in Hbound. lia.
Qed.

(** a^k の位数: ord(a^k) = ord(a) / gcd(k, ord(a))

    d = ord(a), g = gcd(k,d), q = d/g とおき、k = g*k'、d = g*q' と分解する。
    1. (a^k)^q' = e: k*q' = d*k' より gpow_nat_mul を使う。
    2. ord(a^k) | q': (1) と mult_order_p_divides から。
    3. q' | ord(a^k): a^(k*m)=e → d|k*m → q'|k'*m
                      → gcd(q',k')=1 (Nat.gcd_div_gcd) → Nat.gauss → q'|m。
    4. Nat.divide_antisym で等号を導く。 *)
Lemma order_of_power_gcd :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (a : carrier (znz_units_group p Hp)) (k : nat),
    mult_order_p p Hp Hprime (gpow_nat (znz_units_group p Hp) a k) =
    Nat.div (mult_order_p p Hp Hprime a) (Nat.gcd k (mult_order_p p Hp Hprime a)).
Proof.
  intros p Hp Hprime a k.
  set (G := znz_units_group p Hp).
  set (d := mult_order_p p Hp Hprime a).
  set (g := Nat.gcd k d).
  set (b := gpow_nat G a k).
  set (m_b := mult_order_p p Hp Hprime b).
  (* d > 0, g ≠ 0 *)
  assert (Hd_pos : (0 < d)%nat).
  { unfold d, mult_order_p.
    exact (proj1 (mult_order_spec G (p-1) (prime_units_group_order p Hp Hprime) a)). }
  assert (Hg_ne0 : g <> 0%nat).
  { intro Hg0.
    destruct (Nat.gcd_divide_r k d) as [j Hj].
    unfold g in Hg0. rewrite Hg0 in Hj. simpl in Hj. lia. }
  (* k = g * k', d = g * q' *)
  destruct (Nat.gcd_divide_l k d) as [k' Hk'].
  destruct (Nat.gcd_divide_r k d) as [q' Hq'].
  fold g in Hk'. fold g in Hq'.  (* Hk' : k = k' * g, Hq' : d = q' * g *)
  assert (Hq_eq : (d / g = q')%nat).
  { rewrite Hq'. apply Nat.div_mul. exact Hg_ne0. }
  assert (Hk'_eq : (k / g = k')%nat).
  { rewrite Hk'. apply Nat.div_mul. exact Hg_ne0. }
  (* (a^k)^q' = e *)
  assert (Had_e : gpow_nat G a d = e G) by exact (mult_order_p_pow_is_e p Hp Hprime a).
  assert (Hbq_e : gpow_nat G b q' = e G).
  { unfold b. rewrite <- gpow_nat_mul.
    replace (k * q')%nat with (d * k')%nat by (rewrite Hk', Hq'; nia).
    rewrite gpow_nat_mul. rewrite Had_e. apply gpow_nat_e. }
  (* m_b | q' *)
  assert (Hmb_dvd_q' : Nat.divide m_b q').
  { apply (proj1 (mult_order_p_divides p Hp Hprime b q')). exact Hbq_e. }
  (* q' | m_b *)
  assert (Hq'_dvd_mb : Nat.divide q' m_b).
  { assert (Hbmb_e : gpow_nat G b m_b = e G).
    { apply (proj2 (mult_order_p_divides p Hp Hprime b m_b)). apply Nat.divide_refl. }
    assert (Hakm_e : gpow_nat G a (k * m_b) = e G).
    { rewrite gpow_nat_mul. exact Hbmb_e. }
    assert (Hdvd_km : Nat.divide d (k * m_b)).
    { exact (proj1 (mult_order_p_divides p Hp Hprime a (k * m_b)) Hakm_e). }
    assert (Hq'_k'm : Nat.divide q' (k' * m_b)).
    { apply (proj1 (Nat.mul_divide_cancel_l q' (k' * m_b) g Hg_ne0)).
      replace (g * q')%nat with d by (rewrite Hq'; nia).
      replace (g * (k' * m_b))%nat with (k * m_b)%nat by (rewrite Hk'; nia).
      exact Hdvd_km. }
    assert (Hcop : Nat.gcd q' k' = 1%nat).
    { assert (H2 : g = Nat.gcd d k) by (unfold g; apply Nat.gcd_comm).
      pose proof (Nat.gcd_div_gcd d k g Hg_ne0 H2) as H.
      rewrite Hq_eq, Hk'_eq in H. exact H. }
    exact (Nat.gauss q' k' m_b Hq'_k'm Hcop). }
  (* m_b = q' = d / g *)
  rewrite Hq_eq.
  exact (Nat.divide_antisym m_b q' Hmb_dvd_q' Hq'_dvd_mb).
Qed.

(** リストに要素が含まれるなら長さは正 *)
Lemma list_length_pos_of_in : forall {A : Type} (L : list A) (x : A),
  List.In x L -> (0 < List.length L)%nat.
Proof.
  intros A L x HIn. destruct L.
  - inversion HIn.
  - simpl. lia.
Qed.

(** euler_phi n ≥ 1 for n ≥ 1
    gcd(0,1)=1 (n=1の場合) または gcd(1,n)=1 (n≥2の場合) により
    filter に少なくとも1要素が含まれる。 *)
Lemma euler_phi_pos : forall n : nat, (1 <= n)%nat -> (1 <= euler_phi n)%nat.
Proof.
  intros n Hn.
  destruct n as [| n']. { lia. }
  unfold euler_phi.
  apply (list_length_pos_of_in _
    (if Nat.eqb n' 0 then 0%nat else 1%nat)).
  apply List.filter_In.
  destruct n' as [| n''].
  - (* n = 1: k = 0, gcd(0,1)=1 *)
    split.
    + apply List.in_seq. simpl. lia.
    + simpl. reflexivity.
  - (* n >= 2: k = 1, gcd(1,n)=1 *)
    split.
    + apply List.in_seq. simpl. lia.
    + simpl. reflexivity.
Qed.

(** (Z/pZ)* の全要素リスト *)
Definition znz_units_all (p : nat) (Hp : (1 < p)%nat) : list (carrier (znz_units_group p Hp)) :=
  let G := znz_units_group p Hp in
  let Hord := prime_units_group_order p Hp in
  epsilon (inhabits [])
    (fun L => List.NoDup L /\ List.length L = (p - 1)%nat /\
              forall x : carrier G, List.In x L).

(** znz_units_all は正しいリストを返す *)
Lemma znz_units_all_spec : forall (p : nat) (Hp : (1 < p)%nat)
    (Hprime : prime (Z.of_nat p)),
  List.NoDup (znz_units_all p Hp) /\
  List.length (znz_units_all p Hp) = (p - 1)%nat /\
  forall x : carrier (znz_units_group p Hp), List.In x (znz_units_all p Hp).
Proof.
  intros p Hp Hprime.
  unfold znz_units_all.
  apply epsilon_spec.
  pose proof (group_elements_list (znz_units_group p Hp) (p - 1)
                (prime_units_group_order p Hp Hprime)) as [L [HND [Hlen Hall]]].
  exact (ex_intro _ L (conj HND (conj Hlen Hall))).
Qed.

(** 約数リスト: {d ∈ {1,...,n} | d | n} *)
Definition nat_divisors (n : nat) : list nat :=
  List.filter (fun d => Nat.eqb 0 (n mod d)%nat) (List.seq 1 n).

(** nat_divisors の仕様: d ∈ nat_divisors n ↔ 1 ≤ d ≤ n ∧ d | n *)
Lemma nat_divisors_spec : forall (n d : nat),
  (1 <= n)%nat ->
  List.In d (nat_divisors n) <->
    (1 <= d)%nat /\ (d <= n)%nat /\ Nat.divide d n.
Proof.
  intros n d Hn.
  unfold nat_divisors.
  rewrite List.filter_In, List.in_seq.
  split.
  - intros [[H1 H2] Heq].
    split; [lia|]. split; [lia|].
    apply Nat.eqb_eq in Heq.
    exists (n / d)%nat.
    assert (Hd : (d <> 0)%nat) by lia.
    pose proof (Nat.div_mod n d Hd) as Hdm.
    lia.
  - intros [H1 [H2 [k Hk]]].
    split; [lia|].
    apply Nat.eqb_eq.
    subst n. symmetry. apply Nat.mod_mul. lia.
Qed.

(** nat_divisors n は n 自身を含む (n ≥ 1) *)
Lemma nat_divisors_self : forall n : nat, (1 <= n)%nat ->
  List.In n (nat_divisors n).
Proof.
  intros n Hn.
  unfold nat_divisors.
  apply List.filter_In. split.
  - apply List.in_seq. lia.
  - apply Nat.eqb_eq. symmetry. apply Nat.mod_same. lia.
Qed.

Local Open Scope nat_scope.


(** ===================================================================== *)
(** 補助補題: 約数和公式・原始根存在定理の証明に必要な補助補題              *)
(** ===================================================================== *)

(** fold_right add 0 の和分解 *)
Lemma fold_right_add_map_add : forall (A : Type) (f g : A -> nat) (L : list A),
  List.fold_right Nat.add 0%nat (List.map (fun x => (f x + g x)%nat) L) =
  (List.fold_right Nat.add 0%nat (List.map f L) + List.fold_right Nat.add 0%nat (List.map g L))%nat.
Proof.
  intros A f g L. induction L as [|h t IH]; simpl; lia.
Qed.

(** filter (h::t) の長さ分解 *)
Lemma filter_cons_length : forall (A : Type) (f : A -> bool) (h : A) (t : list A),
  List.length (List.filter f (h :: t)) =
  (List.length (List.filter f t) + (if f h then 1%nat else 0%nat))%nat.
Proof.
  intros A f h t. simpl. destruct (f h); simpl; lia.
Qed.

(** 指示関数の sum: x ∉ L ならば sum = 0 *)
Lemma fold_indicator_not_in : forall (A : Type) (eq_dec : forall a b : A, {a = b} + {a <> b})
  (x : A) (L : list A),
  ~List.In x L ->
  List.fold_right Nat.add 0%nat (List.map (fun y => if eq_dec x y then 1%nat else 0%nat) L) = 0%nat.
Proof.
  intros A eq_dec x L HnotIn.
  induction L as [|h t IH]; simpl.
  - reflexivity.
  - destruct (eq_dec x h) as [Heq | Hne].
    + exfalso. apply HnotIn. left. symmetry. exact Heq.
    + simpl. apply IH. intro Hin. apply HnotIn. right. exact Hin.
Qed.

(** 指示関数の sum: x ∈ NoDup L ならば sum = 1 *)
Lemma sum_indicator_one : forall (A : Type) (eq_dec : forall a b : A, {a = b} + {a <> b})
  (x : A) (L : list A),
  List.In x L -> List.NoDup L ->
  List.fold_right Nat.add 0%nat (List.map (fun y => if eq_dec x y then 1%nat else 0%nat) L) = 1%nat.
Proof.
  intros A eq_dec x L HIn HND.
  induction L as [|h t IH]; [inversion HIn|].
  simpl. inversion HND as [|h' t' Hnot HNDt [Hh' Ht']]. subst h' t'.
  destruct HIn as [Heq | HIn'].
  - subst h. destruct (eq_dec x x) as [_ | Hne].
    2: (exfalso; exact (Hne eq_refl)).
    simpl. rewrite fold_indicator_not_in; [lia | exact Hnot].
  - destruct (eq_dec x h) as [Heq | Hne].
    + exfalso. apply Hnot. subst h. exact HIn'.
    + simpl. apply IH; assumption.
Qed.

(** 全要素が 0 の map の fold_right は 0 *)
Lemma fold_right_add_map_zero : forall (A : Type) (f : A -> nat) (L : list A),
  (forall x, List.In x L -> f x = 0%nat) ->
  List.fold_right Nat.add 0%nat (List.map f L) = 0%nat.
Proof.
  intros A f L H. induction L as [|h t IH]; simpl.
  - reflexivity.
  - rewrite H; [simpl; apply IH | left; reflexivity].
    intros x Hx. apply H. right. exact Hx.
Qed.

(** 分割和の定理:
    NoDup な L と NoDup な D があり、f : L → D ならば
    ∑_{d ∈ D} |{x ∈ L : f x = d}| = |L| *)
Lemma partition_sum_length : forall (A B : Type)
  (eq_dec : forall a b : B, {a = b} + {a <> b})
  (L : list A) (D : list B) (f : A -> B),
  List.NoDup L ->
  List.NoDup D ->
  (forall x, List.In x L -> List.In (f x) D) ->
  List.fold_right Nat.add 0%nat
    (List.map (fun d => List.length (List.filter (fun x => if eq_dec (f x) d then true else false) L)) D)
  = List.length L.
Proof.
  intros A B eq_dec L D f HND_L HND_D Hf.
  induction L as [|h t IH].
  - simpl. apply fold_right_add_map_zero. intros d _. simpl. reflexivity.
  - inversion HND_L as [|h' t' Hnot HNDt [Hh' Ht']]. subst h' t'.
    pose proof (Hf h (or_introl eq_refl)) as Hfh_in.
    assert (Hmap : forall d,
      List.length (List.filter (fun x => if eq_dec (f x) d then true else false) (h :: t)) =
      (List.length (List.filter (fun x => if eq_dec (f x) d then true else false) t) +
                   (if eq_dec (f h) d then 1%nat else 0%nat))%nat).
    { intro d. rewrite filter_cons_length. destruct (eq_dec (f h) d); simpl; lia. }
    rewrite (List.map_ext _ _ Hmap), fold_right_add_map_add, IH; try assumption.
    2: { intros x Hx. apply Hf. right. exact Hx. }
    assert (Hind1 : List.fold_right Nat.add 0%nat (List.map (fun d => if eq_dec (f h) d then 1%nat else 0%nat) D) = 1%nat).
    { apply (sum_indicator_one B eq_dec (f h) D Hfh_in HND_D). }
    simpl. lia.
Qed.

(** nat_divisors は NoDup *)
Lemma nat_divisors_NoDup : forall n : nat, List.NoDup (nat_divisors n).
Proof.
  intro n. unfold nat_divisors. apply List.NoDup_filter. apply List.seq_NoDup.
Qed.

(** mult_order_p の nat_divisors (p-1) *)
Lemma mult_order_p_in_nat_divisors :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (x : carrier (znz_units_group p Hp)),
  List.In (mult_order_p p Hp Hprime x) (nat_divisors (p - 1)).
Proof.
  intros p Hp Hprime x.
  apply (nat_divisors_spec (p - 1) (mult_order_p p Hp Hprime x)).
  { lia. }
  split.
  { unfold mult_order_p.
    exact (proj1 (mult_order_spec (znz_units_group p Hp) (p-1)
      (prime_units_group_order p Hp Hprime) x)). }
  split.
  { destruct (mult_order_p_divides_p_minus_1 p Hp Hprime x) as [k Hk].
    assert (Hk_pos : k <> 0%nat).
    { intro Hz. subst k. simpl in Hk.
      unfold mult_order_p in Hk.
      pose proof (proj1 (mult_order_spec (znz_units_group p Hp) (p-1)
        (prime_units_group_order p Hp Hprime) x)) as Hord_pos.
      lia. }
    nia. }
  exact (mult_order_p_divides_p_minus_1 p Hp Hprime x).
Qed.

(** Z の divisibility から Nat の divisibility へ変換 *)
Lemma nat_divide_Z : forall m n : nat,
  Nat.divide m n -> (Z.of_nat m | Z.of_nat n)%Z.
Proof.
  intros m n [k Hk]. exists (Z.of_nat k). rewrite Hk. rewrite Nat2Z.inj_mul. lia.
Qed.

(** Z の divisibility から Nat の divisibility へ逆変換 *)
Lemma Z_divide_nat : forall m n : nat,
  (Z.of_nat m | Z.of_nat n)%Z -> Nat.divide m n.
Proof.
  intros m n [k Hk].
  destruct m as [|m'].
  - exists 0%nat. apply Nat2Z.inj. simpl. lia.
  - assert (Hk_nn : (0 <= k)%Z).
    { destruct (Z.lt_ge_cases k 0%Z) as [Hk_neg | Hk_nn]. 2: exact Hk_nn.
      exfalso. assert (H : (k * Z.of_nat (S m') < 0)%Z) by (apply Z.mul_neg_pos; lia). lia. }
    exists (Z.to_nat k). apply Nat2Z.inj. rewrite Nat2Z.inj_mul.
    rewrite Z2Nat.id by exact Hk_nn. lia.
Qed.

(** Z.gcd と Nat.gcd の関係 *)
Lemma Z_gcd_of_nat : forall m n : nat,
  Z.gcd (Z.of_nat m) (Z.of_nat n) = Z.of_nat (Nat.gcd m n).
Proof.
  intros m n. apply Z.gcd_unique; [apply Nat2Z.is_nonneg | apply nat_divide_Z; apply Nat.gcd_divide_l |
  apply nat_divide_Z; apply Nat.gcd_divide_r |].
  intros d Hdm Hdn. apply Z.divide_abs_l.
  assert (Habs_eq : Z.abs d = Z.of_nat (Z.to_nat (Z.abs d))).
  { symmetry. apply Z2Nat.id. apply Z.abs_nonneg. }
  rewrite Habs_eq. apply nat_divide_Z. apply Nat.gcd_greatest.
  - apply Z_divide_nat. rewrite <- Habs_eq. apply Z.divide_abs_l. exact Hdm.
  - apply Z_divide_nat. rewrite <- Habs_eq. apply Z.divide_abs_l. exact Hdn.
Qed.

(** euler_phi を Nat.gcd で書き換え *)
Lemma euler_phi_nat_gcd : forall n : nat,
  euler_phi n =
  List.length (List.filter (fun k => Nat.eqb (Nat.gcd k n) 1) (List.seq 0 n)).
Proof.
  intro n. unfold euler_phi. f_equal. apply List.filter_ext. intro k.
  rewrite Z_gcd_of_nat.
  destruct (Nat.eqb (Nat.gcd k n) 1) eqn:Heqb.
  - apply Nat.eqb_eq in Heqb. rewrite Heqb. reflexivity.
  - apply Z.eqb_neq.
    intro Heq.
    assert (Hnat : (Nat.gcd k n = 1)%nat).
    { zify. lia. }
    rewrite Hnat in Heqb. discriminate Heqb.
Qed.

(** n >= 1 のとき gcd(k,n) >= 1 *)
Lemma nat_gcd_ge_one : forall k n : nat, (1 <= n)%nat -> (1 <= Nat.gcd k n)%nat.
Proof.
  intros k n Hn.
  pose proof (Nat.gcd_divide_r k n) as [q Hq].
  destruct (Nat.gcd k n) as [|g]; [simpl in Hq; lia | lia].
Qed.

(** n >= 1 のとき gcd(k,n) <= n *)
Lemma nat_gcd_le_n : forall k n : nat, (1 <= n)%nat -> (Nat.gcd k n <= n)%nat.
Proof.
  intros k n Hn.
  pose proof (Nat.gcd_divide_r k n) as [q Hq].
  destruct q as [|q']; [simpl in Hq; lia|].
  destruct (Nat.gcd k n) as [|g']; [simpl in Hq; lia | nia].
Qed.

(** k ∈ seq 0 n のとき gcd(k,n) ∈ nat_divisors n *)
Lemma nat_gcd_in_nat_divisors : forall n k : nat,
  (1 <= n)%nat -> List.In k (List.seq 0 n) ->
  List.In (Nat.gcd k n) (nat_divisors n).
Proof.
  intros n k Hn _.
  unfold nat_divisors. apply List.filter_In. split.
  - apply List.in_seq. split.
    + exact (nat_gcd_ge_one k n Hn).
    + pose proof (nat_gcd_le_n k n Hn). lia.
  - apply Nat.eqb_eq. symmetry.
    destruct (Nat.gcd_divide_r k n) as [q Hq].
    rewrite Hq at 1. apply Nat.Div0.mod_mul.
Qed.

(** n/(n/d) = d (d|n, d>=1, n>=1) *)
Lemma div_div_eq : forall n d : nat,
  (1 <= d)%nat -> (1 <= n)%nat -> Nat.divide d n -> (n / (n / d))%nat = d.
Proof.
  intros n d Hd Hn [k Hk].
  assert (Hk0 : (k <> 0)%nat) by (intro Hkz; subst; simpl in Hn; lia).
  subst n. rewrite Nat.div_mul by lia. rewrite Nat.mul_comm. apply Nat.div_mul. lia.
Qed.

(** d|n → n/d|n *)
Lemma divisor_div_closed : forall n d : nat,
  (1 <= n)%nat -> (1 <= d)%nat -> Nat.divide d n -> Nat.divide (n/d) n.
Proof.
  intros n d Hn Hd [k Hk].
  subst n. rewrite Nat.div_mul by lia. exists d. lia.
Qed.

(** fiber の長さ: |{k < n : gcd(k,n) = e}| = |{j < n/e : gcd(j,n/e) = 1}| *)
Lemma fiber_len_eq : forall (n e : nat),
  (1 <= n)%nat -> (1 <= e)%nat -> Nat.divide e n ->
  List.length (List.filter (fun k => Nat.eqb (Nat.gcd k n) e) (List.seq 0 n)) =
  List.length (List.filter (fun j => Nat.eqb (Nat.gcd j (n/e)) 1) (List.seq 0 (n/e))).
Proof.
  intros n e Hn He Hdvd.
  assert (He' : (e <> 0)%nat) by lia.
  assert (Hn_eq : n = n/e * e).
  { destruct Hdvd as [k Hk]. subst n. rewrite Nat.div_mul by exact He'. lia. }
  set (m := (n/e)%nat). fold m in Hn_eq.
  set (Lk := List.filter (fun k => Nat.eqb (Nat.gcd k n) e) (List.seq 0 n)).
  set (Lj := List.filter (fun j => Nat.eqb (Nat.gcd j m) 1) (List.seq 0 m)).
  apply Nat.le_antisymm.
  - rewrite <- (List.length_map (fun k => k/e) Lk).
    apply List.NoDup_incl_length.
    + apply List.NoDup_map_NoDup_ForallPairs.
      * intros k1 k2 Hk1 Hk2 Heq.
        apply List.filter_In in Hk1, Hk2.
        destruct Hk1 as [_ Hk1_gcd], Hk2 as [_ Hk2_gcd].
        apply Nat.eqb_eq in Hk1_gcd, Hk2_gcd.
        assert (He_dvd_k1 : Nat.divide e k1). { rewrite <- Hk1_gcd. apply Nat.gcd_divide_l. }
        assert (He_dvd_k2 : Nat.divide e k2). { rewrite <- Hk2_gcd. apply Nat.gcd_divide_l. }
        destruct He_dvd_k1 as [j1 Hj1], He_dvd_k2 as [j2 Hj2].
        assert (Hj1e : k1/e = j1) by (rewrite Hj1; apply Nat.div_mul; lia).
        assert (Hj2e : k2/e = j2) by (rewrite Hj2; apply Nat.div_mul; lia).
        rewrite Hj1e, Hj2e in Heq. subst j2. lia.
      * apply List.NoDup_filter. apply List.seq_NoDup.
    + intros k Hk_in.
      apply List.in_map_iff in Hk_in.
      destruct Hk_in as [k0 [Heq Hk0_in]].
      apply List.filter_In in Hk0_in.
      destruct Hk0_in as [Hk0_seq Hk0_gcd].
      apply Nat.eqb_eq in Hk0_gcd.
      assert (He_dvd_k0 : Nat.divide e k0). { rewrite <- Hk0_gcd. apply Nat.gcd_divide_l. }
      destruct He_dvd_k0 as [j Hj].
      assert (Hje : k0/e = j) by (rewrite Hj; apply Nat.div_mul; lia).
      rewrite Hje in Heq. subst k.
      apply List.filter_In. split.
      * apply List.in_seq. split. lia. apply List.in_seq in Hk0_seq. rewrite Hn_eq in Hk0_seq. nia.
      * apply Nat.eqb_eq.
        assert (Hgcd : Nat.gcd (j*e) (m*e) = Nat.gcd j m * e) by apply Nat.gcd_mul_mono_r.
        rewrite <- Hj, <- Hn_eq in Hgcd. rewrite Hk0_gcd in Hgcd. nia.
  - rewrite <- (List.length_map (fun j => j*e) Lj).
    apply List.NoDup_incl_length.
    + apply List.NoDup_map_NoDup_ForallPairs.
      * intros j1 j2 _ _ Heq. nia.
      * apply List.NoDup_filter. apply List.seq_NoDup.
    + intros k Hk_in.
      apply List.in_map_iff in Hk_in.
      destruct Hk_in as [j [Heq Hj_in]].
      apply List.filter_In in Hj_in.
      destruct Hj_in as [Hj_seq Hj_gcd].
      apply Nat.eqb_eq in Hj_gcd.
      apply List.filter_In. split.
      * apply List.in_seq. split. lia. apply List.in_seq in Hj_seq. rewrite Hn_eq. nia.
      * apply Nat.eqb_eq. subst k.
        assert (Hgcd : Nat.gcd (j*e) (m*e) = Nat.gcd j m * e) by apply Nat.gcd_mul_mono_r.
        rewrite <- Hn_eq in Hgcd. rewrite Hj_gcd in Hgcd. lia.
Qed.

(** fiber の長さ = euler_phi (n/e) *)
Lemma fiber_len_eq_phi : forall (n e : nat),
  (1 <= n)%nat -> (1 <= e)%nat -> Nat.divide e n ->
  List.length (List.filter (fun k => Nat.eqb (Nat.gcd k n) e) (List.seq 0 n)) =
  euler_phi (n/e).
Proof.
  intros n e Hn He Hdvd.
  rewrite fiber_len_eq by assumption.
  rewrite <- euler_phi_nat_gcd. reflexivity.
Qed.

(** nat_divisors n は d ↦ n/d で自分自身と Permutation *)
Lemma divisors_perm : forall n : nat, (1 <= n)%nat ->
  Permutation (nat_divisors n) (List.map (fun d => n/d) (nat_divisors n)).
Proof.
  intros n Hn.
  apply NoDup_Permutation.
  - apply nat_divisors_NoDup.
  - apply List.NoDup_map_NoDup_ForallPairs.
    + intros d1 d2 Hd1_in Hd2_in Heq.
      apply (nat_divisors_spec n d1 Hn) in Hd1_in.
      apply (nat_divisors_spec n d2 Hn) in Hd2_in.
      destruct Hd1_in as [Hd1_ge [_ Hd1_dvd]].
      destruct Hd2_in as [Hd2_ge [_ Hd2_dvd]].
      pose proof (div_div_eq n d1 Hd1_ge Hn Hd1_dvd) as H1.
      pose proof (div_div_eq n d2 Hd2_ge Hn Hd2_dvd) as H2.
      rewrite Heq in H1. lia.
    + apply nat_divisors_NoDup.
  - intro d. split.
    + intro Hd_in.
      apply (nat_divisors_spec n d Hn) in Hd_in.
      destruct Hd_in as [Hd_ge [Hd_le Hd_dvd]].
      assert (Hnd_dvd : Nat.divide (n/d) n) by (apply divisor_div_closed; assumption).
      assert (Hnd_ge : 1 <= n/d).
      { destruct Hd_dvd as [k Hk]. subst n. rewrite Nat.div_mul by lia. lia. }
      apply List.in_map_iff. exists (n/d). split.
      * exact (div_div_eq n d Hd_ge Hn Hd_dvd).
      * apply (nat_divisors_spec n (n/d) Hn). split; [exact Hnd_ge|]. split.
        { destruct Hd_dvd as [k Hk]. subst n. rewrite Nat.div_mul by lia. nia. }
        exact Hnd_dvd.
    + intro Hd_in. apply List.in_map_iff in Hd_in.
      destruct Hd_in as [d' [Heq Hd'_in]].
      apply (nat_divisors_spec n d' Hn) in Hd'_in.
      destruct Hd'_in as [Hd'_ge [_ Hd'_dvd]]. subst d.
      apply (nat_divisors_spec n (n/d') Hn). split.
      { destruct Hd'_dvd as [k Hk]. subst n. rewrite Nat.div_mul by lia. lia. }
      split.
      { destruct Hd'_dvd as [k Hk]. subst n. rewrite Nat.div_mul by lia. nia. }
      exact (divisor_div_closed n d' Hn Hd'_ge Hd'_dvd).
Qed.

(** Permutation なら fold_right add 0 は等しい *)
Lemma fold_right_Permutation : forall (L1 L2 : list nat),
  Permutation L1 L2 ->
  List.fold_right Nat.add 0%nat L1 = List.fold_right Nat.add 0%nat L2.
Proof.
  intros L1 L2 Hperm. induction Hperm; simpl; lia.
Qed.


(** ===================================================================== *)
(** 約数和公式: ∑_{d|n} φ(d) = n                                          *)
(** ===================================================================== *)

(** 証明:
    1. partition_sum_length を L=seq 0 n, D=nat_divisors n, f=gcd(·,n) に適用
    2. 各 fiber |{k<n: gcd(k,n)=d}| = euler_phi(n/d) を fiber_len_eq_phi で示す
    3. divisors_perm で ∑ euler_phi(n/d) = ∑ euler_phi d を得る *)
Lemma sum_phi_over_divisors : forall n : nat,
  (1 <= n)%nat ->
  List.fold_right Nat.add 0%nat
    (List.map euler_phi (nat_divisors n)) = n.
Proof.
  intros n Hn.
  assert (Hpart : List.fold_right Nat.add 0%nat
    (List.map (fun d => List.length (List.filter (fun k => if Nat.eq_dec (Nat.gcd k n) d then true else false) (List.seq 0 n)))
    (nat_divisors n)) = List.length (List.seq 0 n)).
  { apply partition_sum_length.
    - apply List.seq_NoDup.
    - apply nat_divisors_NoDup.
    - intros k Hk_in. apply nat_gcd_in_nat_divisors; assumption. }
  rewrite List.length_seq in Hpart.
  assert (Hmap_eq : List.map (fun d => List.length (List.filter (fun k => if Nat.eq_dec (Nat.gcd k n) d then true else false) (List.seq 0 n))) (nat_divisors n) =
    List.map (fun d => euler_phi (n/d)) (nat_divisors n)).
  { apply List.map_ext_in. intros d Hd_in.
    apply (nat_divisors_spec n d Hn) in Hd_in.
    destruct Hd_in as [Hd_ge [_ Hd_dvd]].
    assert (Hfilter_eq : List.filter (fun k => if Nat.eq_dec (Nat.gcd k n) d then true else false) (List.seq 0 n) =
      List.filter (fun k => Nat.eqb (Nat.gcd k n) d) (List.seq 0 n)).
    { apply List.filter_ext_in. intros k _.
      destruct (Nat.eq_dec (Nat.gcd k n) d) as [Heq | Hne];
      [rewrite Heq; symmetry; apply Nat.eqb_refl | symmetry; apply Nat.eqb_neq; exact Hne]. }
    rewrite Hfilter_eq.
    exact (fiber_len_eq_phi n d Hn Hd_ge Hd_dvd). }
  rewrite Hmap_eq in Hpart.
  assert (Hperm_eq : List.fold_right Nat.add 0%nat (List.map (fun d => euler_phi (n/d)) (nat_divisors n)) =
    List.fold_right Nat.add 0%nat (List.map euler_phi (nat_divisors n))).
  { pose proof (divisors_perm n Hn) as Hperm.
    assert (Hmap_perm : Permutation (List.map (fun d => euler_phi (n/d)) (nat_divisors n))
                                    (List.map euler_phi (nat_divisors n))).
    { pose proof (Permutation_map euler_phi (Permutation_sym Hperm)) as Hp2.
      rewrite List.map_map in Hp2. exact Hp2. }
    apply fold_right_Permutation. exact Hmap_perm. }
  lia.
Qed.



Local Close Scope nat_scope.
(** 位数 d の元の個数: ψ(d) の定義 *)
Definition psi (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
    (d : nat) : nat :=
  List.length (List.filter
    (fun x => Nat.eqb (mult_order_p p Hp Hprime x) d)
    (znz_units_all p Hp)).

(** ===================================================================== *)
(** psi_le_phi: ψ(d) ≤ φ(d) for all d | (p-1)                           *)
(** ===================================================================== *)

(** 空でないリストから要素を取り出す *)
Lemma list_nonempty_has_elem : forall (A : Type) (L : list A),
  (0 < List.length L)%nat -> exists x, List.In x L.
Proof.
  intros A L H. destruct L as [|h t].
  - simpl in H. lia.
  - exists h. left. reflexivity.
Qed.

(** 各 d | (p-1) に対して ψ(d) ≤ φ(d)
    証明:
    - ψ(d) = 0 の場合: 自明
    - ψ(d) ≥ 1 の場合: 位数 d の元 a を取り、epsilon で各 x に k を対応させる単射を構成 *)
Lemma psi_le_phi : forall (p : nat) (Hp : (1 < p)%nat)
    (Hprime : prime (Z.of_nat p)) (d : nat),
  Nat.divide d (p - 1) ->
  (psi p Hp Hprime d <= euler_phi d)%nat.
Proof.
  intros p Hp Hprime d Hdvd.
  (* d = 0 の場合: p-1 = 0 → p = 1, 矛盾 *)
  destruct (Nat.eq_dec d 0%nat) as [Hd0 | Hd_pos].
  - subst d. destruct Hdvd as [k Hk]. lia.
  - (* d ≥ 1 の場合 *)
    assert (Hd_ge : (0 < d)%nat) by lia.
    (* psi d = 0 の場合: 0 <= euler_phi d は自明 *)
    destruct (Nat.eq_dec (psi p Hp Hprime d) 0%nat) as [Hz | Hnz].
    + rewrite Hz. apply Nat.le_0_l.
    + assert (Hpsi_pos : (0 < psi p Hp Hprime d)%nat) by lia.
      unfold psi in Hpsi_pos.
      set (G := znz_units_group p Hp).
      set (Lx := List.filter (fun x => Nat.eqb (mult_order_p p Hp Hprime x) d) (znz_units_all p Hp)).
      set (Lk := List.filter (fun k => Nat.eqb (Nat.gcd k d) 1) (List.seq 0 d)).
      fold Lx in Hpsi_pos.
      pose proof (list_nonempty_has_elem _ Lx Hpsi_pos) as [a Ha_in].
      apply List.filter_In in Ha_in.
      destruct Ha_in as [_ Ha_ord].
      apply Nat.eqb_eq in Ha_ord.
      (* a には位数 d がある *)
      (* 単射 Lx → Lk を epsilon で構成: x ↦ k where a^k = x *)
      set (k_of_x := fun x => epsilon (inhabits 0%nat)
        (fun k => (k < d)%nat /\ gpow_nat G a k = x)).
      (* psi d ≤ euler_phi d: length Lx ≤ length Lk *)
      assert (Hmain : (List.length (List.map k_of_x Lx) <= List.length Lk)%nat).
      { apply List.NoDup_incl_length.
      * apply List.NoDup_map_NoDup_ForallPairs.
        -- intros x1 x2 Hx1 Hx2 Hk_eq.
           apply List.filter_In in Hx1, Hx2.
           destruct Hx1 as [_ Hx1_ord], Hx2 as [_ Hx2_ord].
           apply Nat.eqb_eq in Hx1_ord, Hx2_ord.
           assert (Hx1d : gpow_nat G x1 d = e G).
           { rewrite <- Hx1_ord. exact (mult_order_p_pow_is_e p Hp Hprime x1). }
           assert (Hx2d : gpow_nat G x2 d = e G).
           { rewrite <- Hx2_ord. exact (mult_order_p_pow_is_e p Hp Hprime x2). }
           assert (Hx1_ex : exists k, (k < d)%nat /\ gpow_nat G a k = x1).
           { apply (order_d_elements_are_powers p Hp Hprime a d Hd_ge Ha_ord x1 Hx1d). }
           assert (Hx2_ex : exists k, (k < d)%nat /\ gpow_nat G a k = x2).
           { apply (order_d_elements_are_powers p Hp Hprime a d Hd_ge Ha_ord x2 Hx2d). }
           pose proof (epsilon_spec (inhabits 0%nat) _ Hx1_ex) as [Hk1_lt Hk1_eq].
           pose proof (epsilon_spec (inhabits 0%nat) _ Hx2_ex) as [Hk2_lt Hk2_eq].
           (* k_of_x x1 = k_of_x x2 から x1 = x2 *)
           assert (Hx1x2 : x1 = x2).
           { rewrite <- Hk1_eq, <- Hk2_eq.
             unfold k_of_x in Hk_eq. rewrite Hk_eq. reflexivity. }
           exact Hx1x2.
        -- apply List.NoDup_filter. exact (proj1 (znz_units_all_spec p Hp Hprime)).
      * intros k Hk_in.
        apply List.in_map_iff in Hk_in.
        destruct Hk_in as [x [Heq Hx_in]].
        apply List.filter_In in Hx_in.
        destruct Hx_in as [_ Hx_ord].
        apply Nat.eqb_eq in Hx_ord.
        assert (Hxd : gpow_nat G x d = e G).
        { rewrite <- Hx_ord. exact (mult_order_p_pow_is_e p Hp Hprime x). }
        assert (Hx_ex : exists k0, (k0 < d)%nat /\ gpow_nat G a k0 = x).
        { apply (order_d_elements_are_powers p Hp Hprime a d Hd_ge Ha_ord x Hxd). }
        pose proof (epsilon_spec (inhabits 0%nat) _ Hx_ex) as [Hk_lt Hk_eq].
        subst k.
        apply List.filter_In. split.
        -- apply List.in_seq. split. lia. exact Hk_lt.
        -- apply Nat.eqb_eq.
           (* k_of_x x を fold した形で gcd 条件を作る *)
           assert (Hkgcd : Nat.div d (Nat.gcd (k_of_x x) d) = d).
           { pose proof (order_of_power_gcd p Hp Hprime a (k_of_x x)) as Hpow.
             rewrite Ha_ord in Hpow.
             assert (Heq : gpow_nat (znz_units_group p Hp) a (k_of_x x) = x) by exact Hk_eq.
             rewrite Heq in Hpow. rewrite Hx_ord in Hpow.
             exact (eq_sym Hpow). }
           destruct (Nat.gcd (k_of_x x) d) as [|g] eqn:Hgcd_eq.
           ++ exfalso. pose proof (Nat.gcd_divide_r (k_of_x x) d) as [q Hq].
              rewrite Hgcd_eq in Hq. simpl in Hq. lia.
           ++ destruct g as [|g'].
              ** reflexivity.
              ** exfalso.
                 assert (H1lt : (1 < S (S g'))%nat) by lia.
                 pose proof (Nat.div_lt d (S (S g')) Hd_ge H1lt) as Hlt.
                 rewrite Hkgcd in Hlt.
                 exact (Nat.lt_irrefl d Hlt).
}
      rewrite List.length_map in Hmain.
      unfold psi. fold G. fold Lx. rewrite euler_phi_nat_gcd. exact Hmain.
Qed.


(** ===================================================================== *)
(** sum_psi_eq_p_minus_1: ∑_{d|(p-1)} ψ(d) = p-1                        *)
(** ===================================================================== *)

(** ∑_{d|(p-1)} ψ(d) = p-1
    証明: partition_sum_length を L=znz_units_all, D=nat_divisors(p-1),
    f=mult_order_p に適用 *)
Lemma sum_psi_eq_p_minus_1 : forall (p : nat) (Hp : (1 < p)%nat)
    (Hprime : prime (Z.of_nat p)),
  List.fold_right Nat.add 0%nat
    (List.map (psi p Hp Hprime) (nat_divisors (p - 1))) = (p - 1)%nat.
Proof.
  intros p Hp Hprime.
  (* psi d の定義を展開し、partition_sum_length の形に持ち込む *)
  unfold psi.
  (* 目標: fold_right add 0 (map (fun d => length (filter (order=d) units)) divisors) = p-1 *)
  (* これは partition_sum_length の結果 *)
  assert (Hpart : List.fold_right Nat.add 0%nat
    (List.map (fun d => List.length (List.filter (fun x => if Nat.eq_dec (mult_order_p p Hp Hprime x) d then true else false)
      (znz_units_all p Hp))) (nat_divisors (p - 1))) =
    List.length (znz_units_all p Hp)).
  { apply partition_sum_length.
    - exact (proj1 (znz_units_all_spec p Hp Hprime)).
    - apply nat_divisors_NoDup.
    - intros x _. apply (mult_order_p_in_nat_divisors p Hp Hprime x). }
  rewrite (proj1 (proj2 (znz_units_all_spec p Hp Hprime))) in Hpart.
  (* filter の bool 関数を変換 *)
  assert (Hmap_eq : List.map (fun d => List.length (List.filter (fun x => if Nat.eq_dec (mult_order_p p Hp Hprime x) d then true else false)
    (znz_units_all p Hp))) (nat_divisors (p - 1)) =
    List.map (fun d => List.length (List.filter (fun x => Nat.eqb (mult_order_p p Hp Hprime x) d)
    (znz_units_all p Hp))) (nat_divisors (p - 1))).
  { apply List.map_ext. intro d. f_equal. apply List.filter_ext. intro x.
    destruct (Nat.eq_dec (mult_order_p p Hp Hprime x) d) as [Heq | Hne];
    [rewrite Heq; symmetry; apply Nat.eqb_refl | symmetry; apply Nat.eqb_neq; exact Hne]. }
  rewrite <- Hmap_eq. exact Hpart.
Qed.


(** 非負整数リストの和が0なら全要素が0 *)
Lemma nat_sum_zero_all_zero : forall (L : list nat),
  List.fold_right Nat.add 0%nat L = 0%nat ->
  forall x, List.In x L -> x = 0%nat.
Proof.
  intros L Hsum x HIn.
  induction L as [| h t IH].
  - inversion HIn.
  - simpl in Hsum.
    destruct HIn as [Heq | HIn'].
    + subst x. lia.
    + apply IH. lia. exact HIn'.
Qed.

(** ===================================================================== *)
(** primitive_root_exists の補助補題                                       *)
(** ===================================================================== *)

(** 自然数リストの点ごとの ≤ から fold の ≤ *)
Lemma fold_add_map_le : forall (A : Type) (f g : A -> nat) (L : list A),
  (forall x, List.In x L -> (f x <= g x)%nat) ->
  (List.fold_right Nat.add 0%nat (List.map f L) <=
  List.fold_right Nat.add 0%nat (List.map g L))%nat.
Proof.
  intros A f g L H.
  induction L as [|h t IH]; simpl.
  - lia.
  - apply Nat.add_le_mono.
    + exact (H h (or_introl eq_refl)).
    + apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

(** fold が等しく点ごと ≤ ならば点ごとに等しい *)
Lemma fold_add_eq_all_eq : forall (A : Type) (f g : A -> nat) (L : list A),
  List.fold_right Nat.add 0%nat (List.map f L) =
  List.fold_right Nat.add 0%nat (List.map g L) ->
  (forall x, List.In x L -> (f x <= g x)%nat) ->
  forall x, List.In x L -> f x = g x.
Proof.
  intros A f g L Hsum Hle x Hx.
  induction L as [|h t IH].
  - inversion Hx.
  - simpl in Hsum.
    assert (Hfh_le : (f h <= g h)%nat) by (apply Hle; left; reflexivity).
    assert (Hft_le : (List.fold_right Nat.add 0%nat (List.map f t) <=
                     List.fold_right Nat.add 0%nat (List.map g t))%nat).
    { apply fold_add_map_le. intros y Hy. apply Hle. right. exact Hy. }
    destruct Hx as [Heq | Hx'].
    + subst h. lia.
    + apply IH.
      * lia.
      * intros y Hy. apply Hle. right. exact Hy.
      * exact Hx'.
Qed.

(** filter の長さが ≥ 1 なら要素が存在する *)
Lemma filter_nonempty_ex : forall (A : Type) (P : A -> bool) (L : list A),
  (1 <= List.length (List.filter P L))%nat ->
  exists x, List.In x L /\ P x = true.
Proof.
  intros A P L H.
  induction L as [|h t IH].
  - simpl in H. lia.
  - simpl in H. destruct (P h) eqn:Hph.
    + exists h. split; [left; reflexivity | exact Hph].
    + simpl in H. destruct (IH H) as [x [Hx_in Hx_P]].
      exists x. split; [right; exact Hx_in | exact Hx_P].
Qed.

(** ===================================================================== *)
(** primitive_root_exists: 原始根の存在定理                               *)
(** ===================================================================== *)

(** 原始根の存在定理 (Primitive Root Theorem):
    任意の素数 p に対して (Z/pZ)* に位数 p-1 の元 (原始根) が存在する。

    証明:
    1. ψ(d) ≤ φ(d) for all d | (p-1)  [psi_le_phi]
    2. ∑_{d|(p-1)} ψ(d) = p-1           [sum_psi_eq_p_minus_1]
    3. ∑_{d|(p-1)} φ(d) = p-1           [sum_phi_over_divisors]
    4. 2,3 より ∑(φ(d)-ψ(d)) = 0 で各項 ≥ 0 なので ψ(d) = φ(d) for all d.
    5. ψ(p-1) = φ(p-1) ≥ 1 より原始根が存在する。 *)
Theorem primitive_root_exists :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p)),
    exists g : carrier (znz_units_group p Hp),
      mult_order_p p Hp Hprime g = (p - 1)%nat.
Proof.
  intros p Hp Hprime.
  (* p-1 ≥ 1 *)
  assert (Hp1 : (1 <= p - 1)%nat) by lia.
  (* ∑psi = p-1 と ∑phi = p-1 *)
  pose proof (sum_psi_eq_p_minus_1 p Hp Hprime) as Hsum_psi.
  pose proof (sum_phi_over_divisors (p - 1) Hp1) as Hsum_phi.
  (* 各 d | p-1 に対して psi d ≤ phi d *)
  assert (Hle : forall d, List.In d (nat_divisors (p - 1)) ->
    (psi p Hp Hprime d <= euler_phi d)%nat).
  { intros d Hd_in.
    apply (nat_divisors_spec (p-1) d Hp1) in Hd_in.
    destruct Hd_in as [_ [_ Hd_dvd]].
    exact (psi_le_phi p Hp Hprime d Hd_dvd). }
  (* ∑psi = ∑phi かつ点ごと psi ≤ phi → psi (p-1) = phi (p-1) *)
  assert (Heq_p1 : psi p Hp Hprime (p - 1) = euler_phi (p - 1)).
  { apply (fold_add_eq_all_eq nat
      (psi p Hp Hprime) euler_phi (nat_divisors (p - 1))).
    - lia.
    - exact Hle.
    - apply (nat_divisors_self (p - 1) Hp1). }
  (* phi (p-1) ≥ 1 *)
  assert (Hphi_pos : (1 <= euler_phi (p - 1))%nat) by (apply euler_phi_pos; lia).
  (* psi (p-1) ≥ 1 → filter が空でない → 要素が存在する *)
  (* psi(p-1) = phi(p-1) >= 1 *)
  assert (Hpsi_pos : (1 <= psi p Hp Hprime (p - 1))%nat) by (rewrite Heq_p1; exact Hphi_pos).
  unfold psi in Hpsi_pos.
  pose proof (filter_nonempty_ex (carrier (znz_units_group p Hp))
    (fun x => Nat.eqb (mult_order_p p Hp Hprime x) (p - 1))
    (znz_units_all p Hp)
    Hpsi_pos) as [g [_ Hg_ord]].
  apply Nat.eqb_eq in Hg_ord.
  exists g. exact Hg_ord.
Qed.



(** ===================================================================== *)
(** Phase 1: (Z/pZ)* の CyclicGroup 構造                                 *)
(** ===================================================================== *)

(** 原始根による生成:
    位数 p-1 の元 g は (Z/pZ)* の全要素を生成する。

    証明:
      任意の x ∈ (Z/pZ)* に対し、
      フェルマーの小定理より x^(p-1) = e。
      order_d_elements_are_powers より ∃ k < p-1, g^k = x。
      gpow_of_nat で整数冪に変換する。  *)
Lemma primitive_root_generates_all :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p))
         (g : carrier (znz_units_group p Hp)),
    mult_order_p p Hp Hprime g = (p - 1)%nat ->
    forall x : carrier (znz_units_group p Hp),
      exists k : Z, gpow (znz_units_group p Hp) g k = x.
Proof.
  intros p Hp Hprime g Hg x.
  assert (Hp1 : (0 < p - 1)%nat) by lia.
  assert (Hx_e : gpow_nat (znz_units_group p Hp) x (p - 1) =
                 e (znz_units_group p Hp)) by
    exact (fermat_little_theorem p Hp Hprime x).
  destruct (order_d_elements_are_powers p Hp Hprime g (p - 1) Hp1 Hg x Hx_e)
    as [k [_ Heq]].
  exists (Z.of_nat k).
  rewrite gpow_of_nat.
  exact Heq.
Qed.

(** (Z/pZ)* の CyclicGroup 構造:
    primitive_root_exists で生成元 g を取り出し、
    primitive_root_generates_all で巡回性を確認して CyclicGroup レコードを構築する。  *)
Definition znz_units_cyclic_group (p : nat) (Hp : (1 < p)%nat)
    (Hprime : prime (Z.of_nat p)) : CyclicGroup.
Proof.
  (* Prop-existential から Type の値を取り出すために epsilon を使用 *)
  set (g := epsilon (inhabits (e (znz_units_group p Hp)))
    (fun g => mult_order_p p Hp Hprime g = (p - 1)%nat)).
  assert (Hg : mult_order_p p Hp Hprime g = (p - 1)%nat).
  { unfold g. apply epsilon_spec. exact (primitive_root_exists p Hp Hprime). }
  refine {|
    cyclic_group := znz_units_group p Hp;
    generator    := g
  |}.
  exact (primitive_root_generates_all p Hp Hprime g Hg).
Defined.

(** ===================================================================== *)
(** Phase 2: 抽象同型定理 C ≅ Z/nZ                                       *)
(** ===================================================================== *)

(** 位数 n の巡回群の生成元の乗法位数は n に等しい:
    mult_order_spec の最小性から d ≤ n (generator_order より g^n = e)、
    cyclic_group_order_le_period から n ≤ d (g^d = e より)、合わせて d = n。  *)
Lemma generator_mult_order_eq_group_order :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n),
    mult_order C n Hord (generator C) = n.
Proof.
  intros C n Hord.
  set (d := mult_order C n Hord (generator C)).
  assert (Hd_spec := mult_order_spec C n Hord (generator C)).
  fold d in Hd_spec.
  destruct Hd_spec as [Hd_pos [Hd_period Hd_min]].
  assert (Hd_le_n : (d <= n)%nat).
  { apply Hd_min.
    - exact (group_order_pos C n Hord).
    - exact (generator_order C n Hord). }
  assert (Hn_le_d : (n <= d)%nat).
  { apply cyclic_group_order_le_period with (C := C) (m := n) (d := d).
    - exact Hord.
    - exact Hd_pos.
    - exact Hd_period. }
  lia.
Qed.

(** 巡回群の冪の単射性:
    r1 < n, r2 < n, g^r1 = g^r2 ならば r1 = r2。
    generator_mult_order_eq_group_order + mult_order_powers_distinct による。  *)
Lemma cyclic_powers_injective :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n)
         (r1 r2 : nat),
    (r1 < n)%nat -> (r2 < n)%nat ->
    gpow_nat C (generator C) r1 = gpow_nat C (generator C) r2 ->
    r1 = r2.
Proof.
  intros C n Hord r1 r2 Hr1 Hr2 Heq.
  destruct (Nat.eq_dec r1 r2) as [H | H].
  - exact H.
  - exfalso.
    assert (Hr1' : (r1 < mult_order C n Hord (generator C))%nat).
    { rewrite generator_mult_order_eq_group_order. exact Hr1. }
    assert (Hr2' : (r2 < mult_order C n Hord (generator C))%nat).
    { rewrite generator_mult_order_eq_group_order. exact Hr2. }
    exact (mult_order_powers_distinct C n Hord (generator C) r1 r2 Hr1' Hr2' H Heq).
Qed.

(** gpow_nat の周期による簡約:
    g^n = e ならば gpow_nat G g (k mod n) = gpow_nat G g k。
    Nat.div_mod + gpow_nat_period_cancel による。  *)
Lemma gpow_nat_mod :
  forall (G : Group) (g : carrier G) (n k : nat),
    (0 < n)%nat ->
    gpow_nat G g n = e G ->
    gpow_nat G g (k mod n) = gpow_nat G g k.
Proof.
  intros G g n k Hn Hgn.
  set (q := (k / n)%nat).
  set (r := (k mod n)%nat).
  assert (Hk : k = (n * q + r)%nat).
  { unfold q, r. apply Nat.div_mod. lia. }
  rewrite Hk.
  symmetry.
  apply gpow_nat_period_cancel.
  exact Hgn.
Qed.

(** 巡回群インデックスの定義:
    x ∈ C に対して、gpow_nat C (generator C) r = x を満たす
    一意の r < n を epsilon で定義する。  *)
Definition cyc_index (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n)
    (x : carrier C) : nat :=
  epsilon (inhabits 0%nat) (fun r : nat =>
    (r < n)%nat /\ gpow_nat C (generator C) r = x).

(** cyc_index の仕様:
    (1) cyc_index C n Hord x < n
    (2) gpow_nat C (generator C) (cyc_index C n Hord x) = x

    証明: epsilon_spec で存在を示す。
      存在は generator_order + gpow_reduce_mod + gpow_of_nat による。  *)
Lemma cyc_index_spec :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n)
         (x : carrier C),
    (cyc_index C n Hord x < n)%nat /\
    gpow_nat C (generator C) (cyc_index C n Hord x) = x.
Proof.
  intros C n Hord x.
  unfold cyc_index.
  apply epsilon_spec.
  assert (Hn_pos : (0 < n)%nat) by exact (group_order_pos C n Hord).
  assert (Hgn : gpow C (generator C) (Z.of_nat n) = e C)
    by exact (generator_order C n Hord).
  destruct (gpow_reduce_mod C n Hn_pos Hgn x) as [r [Hr Hxr]].
  exists r. split.
  - exact Hr.
  - rewrite gpow_of_nat in Hxr. exact (eq_sym Hxr).
Qed.

(** cyc_index の一意性:
    r < n かつ gpow_nat C g r = x ならば r = cyc_index C n Hord x。
    cyclic_powers_injective + cyc_index_spec による。  *)
Lemma cyc_index_unique :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n)
         (x : carrier C) (r : nat),
    (r < n)%nat ->
    gpow_nat C (generator C) r = x ->
    r = cyc_index C n Hord x.
Proof.
  intros C n Hord x r Hr Heq.
  apply (cyclic_powers_injective C n Hord r (cyc_index C n Hord x)).
  - exact Hr.
  - exact (proj1 (cyc_index_spec C n Hord x)).
  - rewrite Heq.
    exact (eq_sym (proj2 (cyc_index_spec C n Hord x))).
Qed.

(** cyc_index の準同型性:
    cyc_index C n Hord (op C x y) = (cyc_index x + cyc_index y) mod n。

    証明:
      r = cyc_index x, s = cyc_index y として g^r = x, g^s = y。
      g^(r+s) = x * y かつ g^((r+s) mod n) = g^(r+s) [gpow_nat_mod]。
      (r+s) mod n < n なので cyc_index_unique より結論が得られる。  *)
Lemma cyc_index_homo :
  forall (C : CyclicGroup) (n : nat) (Hord : GroupOrder C n)
         (x y : carrier C),
    (cyc_index C n Hord (op C x y) =
    (cyc_index C n Hord x + cyc_index C n Hord y) mod n)%nat.
Proof.
  intros C n Hord x y.
  set (g := generator C).
  set (r := cyc_index C n Hord x).
  set (s := cyc_index C n Hord y).
  assert (Hgr : gpow_nat C g r = x) by exact (proj2 (cyc_index_spec C n Hord x)).
  assert (Hgs : gpow_nat C g s = y) by exact (proj2 (cyc_index_spec C n Hord y)).
  assert (Hn_pos : (0 < n)%nat) by exact (group_order_pos C n Hord).
  assert (Hgn : gpow_nat C g n = e C).
  { rewrite <- gpow_of_nat. exact (generator_order C n Hord). }
  apply eq_sym.
  apply (cyc_index_unique C n Hord (op C x y) ((r + s) mod n)%nat).
  - apply Nat.mod_upper_bound. lia.
  - rewrite <- Hgr, <- Hgs.
    rewrite <- gpow_nat_add.
    fold g.
    apply gpow_nat_mod.
    + exact Hn_pos.
    + exact Hgn.
Qed.

(** 位数 n の巡回群は Z/nZ に同型:

    同型写像 f : carrier C → carrier (znz_group n Hn)
      f(x) = [Z.of_nat (cyc_index C n Hord x)]

    準同型性: cyc_index_homo + Nat2Z.inj_mod + Nat2Z.inj_add
    単射性:   Nat2Z.inj + cyc_index_spec
    全射性:   gpow_nat C g (Z.to_nat k) が k の原像になる  *)
Theorem cyclic_group_isomorphic_znz :
  forall (C : CyclicGroup) (n : nat) (Hn : (0 < n)%nat)
         (Hord : GroupOrder C n),
    C ≅ znz_group n Hn.
Proof.
  intros C n Hn Hord.
  exists (fun x =>
    exist _ (Z.of_nat (cyc_index C n Hord x))
      (conj (Nat2Z.is_nonneg _)
            (proj1 (Nat2Z.inj_lt _ _) (proj1 (cyc_index_spec C n Hord x))))).
  split; [| split].
  - (* 準同型性 *)
    intros x y.
    apply sig_eq. simpl.
    rewrite cyc_index_homo.
    rewrite Nat2Z.inj_mod.
    rewrite Nat2Z.inj_add.
    reflexivity.
  - (* 単射性 *)
    intros x y Hfxy.
    injection Hfxy as Hfxy.
    apply Nat2Z.inj in Hfxy.
    rewrite <- (proj2 (cyc_index_spec C n Hord x)).
    rewrite <- (proj2 (cyc_index_spec C n Hord y)).
    rewrite Hfxy. reflexivity.
  - (* 全射性 *)
    intros [k Hk].
    exists (gpow_nat C (generator C) (Z.to_nat k)).
    apply sig_eq. simpl.
    assert (Hk_nat : (Z.to_nat k < n)%nat).
    { apply (proj2 (Nat2Z.inj_lt _ _)). rewrite Z2Nat.id by lia. lia. }
    rewrite <- (cyc_index_unique C n Hord
      (gpow_nat C (generator C) (Z.to_nat k))
      (Z.to_nat k) Hk_nat (eq_refl _)).
    apply Z2Nat.id. lia.
Qed.

(** ===================================================================== *)
(** Phase 3: 主定理 (Z/pZ)* ≅ Z/(p-1)Z                                  *)
(** ===================================================================== *)

(** 素数 p に対して (Z/pZ)* は Z/(p-1)Z に同型:

    証明:
      1. znz_units_cyclic_group で (Z/pZ)* に CyclicGroup 構造を与える。
      2. prime_units_group_order で GroupOrder (znz_units_group p Hp) (p-1)。
      3. cyclic_group_isomorphic_znz で CyclicGroup C ≅ znz_group (p-1) Hp1。
      4. C の underlying Group は znz_units_group p Hp なので結論を得る。  *)
Theorem znz_units_group_cyclic_iso :
  forall (p : nat) (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p)),
    exists Hp1 : (0 < p - 1)%nat,
      znz_units_group p Hp ≅ znz_group (p - 1) Hp1.
Proof.
  intros p Hp Hprime.
  assert (Hp1 : (0 < p - 1)%nat) by lia.
  exists Hp1.
  set (C := znz_units_cyclic_group p Hp Hprime).
  assert (Hord : GroupOrder C (p - 1)) by
    exact (prime_units_group_order p Hp Hprime).
  exact (cyclic_group_isomorphic_znz C (p - 1) Hp1 Hord).
Qed.

(** ===================================================================== *)
(** (Z/2^nZ)* の構造定理                                                  *)
(** (Z/2^nZ)* ≅ Z/2^(n-2)Z × Z/2Z  (n ≥ 2)                             *)
(** ===================================================================== *)

(** ===== Phase 0: 算術基本事実 ===== *)

(** 2^n > 1 (n ≥ 2):
    Nat.pow_le_mono_r を使い 2^2 ≤ 2^n から導く。 *)
Lemma two_pow_ge2_gt_one : forall n : nat, (2 <= n)%nat -> (1 < 2^n)%nat.
Proof.
  intros n Hn.
  apply Nat.lt_le_trans with (2^2)%nat.
  - simpl. lia.
  - apply Nat.pow_le_mono_r; lia.
Qed.

(** 2^(n-2) > 0 (n ≥ 2):
    帰納法で 0 < 2^m をすべての m に対して証明する。 *)
Lemma two_pow_nm2_pos : forall n : nat, (2 <= n)%nat -> (0 < 2^(n-2))%nat.
Proof.
  intros n _.
  generalize (n - 2)%nat. intro m.
  induction m as [|m' IH].
  - simpl. lia.
  - simpl. apply (proj2 (Nat.lt_0_mul' 2 (2^m'))). split. lia. exact IH.
Qed.

(** euler_phi(2^n) = 2^(n-1) (n ≥ 1):
    euler_phi_prime_pow を p=2, e=n で適用し、(2-1)=1 を処理する。 *)
Lemma euler_phi_two_pow : forall n : nat, (1 <= n)%nat ->
    euler_phi (2^n)%nat = (2^(n-1))%nat.
Proof.
  intros n Hn.
  pose proof (euler_phi_prime_pow 2 n prime_2 Hn) as H.
  simpl in H. rewrite Nat.mul_1_r in H. exact H.
Qed.

(** GroupOrder (znz_units_group (2^n) _) (2^(n-1)) (n ≥ 2):
    euler_phi_two_pow と euler_phi_group_order を組み合わせる。 *)
Lemma znz_units_pow2_order : forall (n : nat) (Hn : (2 <= n)%nat)
    (H2n : (1 < 2^n)%nat),
    GroupOrder (znz_units_group ((2:nat)^n) H2n) (2^(n-1))%nat.
Proof.
  intros n Hn H2n.
  assert (Hn1 : (1 <= n)%nat) by lia.
  rewrite <- (euler_phi_two_pow n Hn1).
  apply euler_phi_group_order.
Qed.

(** キャリア要素の Z.to_nat が n の範囲内であることの補題:
    0 ≤ x かつ x < Z.of_nat n ならば Z.to_nat x < n。 *)
Lemma znz_to_nat_lt : forall (n : nat) (x : Z),
    0 <= x -> x < Z.of_nat n -> (Z.to_nat x < n)%nat.
Proof.
  intros n x H1 H2.
  assert (Hlt : (Z.to_nat x < Z.to_nat (Z.of_nat n))%nat).
  { apply Z2Nat.inj_lt; [exact H1 | lia | exact H2]. }
  rewrite Nat2Z.id in Hlt. exact Hlt.
Qed.

(** GroupOrder (znz_group n Hn) n:
    f(exist _ k _) = Fin.of_nat_lt (Z.to_nat k < n) が全単射。 *)
Lemma znz_group_order_n : forall (n : nat) (Hn : (0 < n)%nat),
    GroupOrder (znz_group n Hn) n.
Proof.
  intros n Hn.
  assert (Hbnd : forall (x : carrier (znz_group n Hn)),
      (Z.to_nat (proj1_sig x) < n)%nat).
  { intro x. exact (znz_to_nat_lt n _ (proj1 (proj2_sig x)) (proj2 (proj2_sig x))). }
  exists (fun x => Fin.of_nat_lt (Hbnd x)).
  split.
  - (* 単射性: Fin.of_nat_lt hx = Fin.of_nat_lt hy → x = y *)
    intros x y Heq.
    apply sig_eq. simpl.
    apply Z2Nat.inj.
    { exact (proj1 (proj2_sig x)). }
    { exact (proj1 (proj2_sig y)). }
    pose proof (to_nat_of_nat_lt _ n (Hbnd x)) as HLx.
    pose proof (to_nat_of_nat_lt _ n (Hbnd y)) as HLy.
    assert (Hk : proj1_sig (Fin.to_nat (Fin.of_nat_lt (Hbnd x))) =
                 proj1_sig (Fin.to_nat (Fin.of_nat_lt (Hbnd y)))).
    { exact (f_equal (fun k => proj1_sig (Fin.to_nat k)) Heq). }
    rewrite HLx in Hk. rewrite HLy in Hk. exact Hk.
  - (* 全射性: 各 i : Fin.t n に対し x0 = [Z.of_nat (Fin.to_nat i)] を構成 *)
    intros i.
    set (m := proj1_sig (Fin.to_nat i)).
    assert (hm : (m < n)%nat) by exact (proj2_sig (Fin.to_nat i)).
    assert (Hrange : (0 <= Z.of_nat m < Z.of_nat n)).
    { split. lia. apply Nat2Z.inj_lt. exact hm. }
    refine (ex_intro _ (exist _ (Z.of_nat m) Hrange) _).
    apply Fin.to_nat_inj.
    rewrite to_nat_of_nat_lt. simpl.
    rewrite Nat2Z.id. reflexivity.
Qed.

(** Fin.t m 上の単射関数は全射でもある (pigeonhole 原理):
    h : Fin.t m → Fin.t m が単射ならば全射。
    証明: h(fin_all m) は NoDup かつ長さ m のリスト。
          j ∉ h(fin_all m) と仮定すると remove j (fin_all m) に含まれるが
          その長さは m-1 < m で矛盾。 *)
Lemma Fin_inj_is_surj : forall (m : nat) (h : Fin.t m -> Fin.t m),
    (forall i j, h i = h j -> i = j) ->
    forall j : Fin.t m, exists i : Fin.t m, h i = j.
Proof.
  intros m h Hinj j.
  assert (Hnd : List.NoDup (List.map h (fin_all m))).
  { apply List.NoDup_map_NoDup_ForallPairs.
    - intros a b _ _ H. exact (Hinj a b H).
    - apply fin_all_NoDup. }
  destruct (List.in_dec Fin.eq_dec j (List.map h (fin_all m))) as [Hin | Hnotin].
  - apply List.in_map_iff in Hin. destruct Hin as [i [Heq _]]. exists i. exact Heq.
  - exfalso.
    assert (Hincl1 : List.incl (List.map h (fin_all m)) (fin_all m)).
    { intros x _. apply fin_all_complete. }
    assert (Hincl2 : List.incl (List.map h (fin_all m))
        (List.remove Fin.eq_dec j (fin_all m))).
    { intros x Hx. apply List.in_in_remove.
      - intro Hxj. subst. exact (Hnotin Hx).
      - apply Hincl1. exact Hx. }
    apply List.NoDup_incl_length in Hincl2; [|exact Hnd].
    rewrite List.map_length, fin_all_length in Hincl2.
    pose proof (List.remove_length_lt Fin.eq_dec (fin_all m) j
        (fin_all_complete m j)) as Hlt.
    rewrite fin_all_length in Hlt.
    lia.
Qed.

(** 単射準同型 + 等位数 → 全射 (全単射):
    f : G → H が準同型・単射で |G| = |H| ならば f は全射でもある。
    証明: GroupOrder の全単射 g : G → Fin.t m と h : H → Fin.t m を使い
          h ∘ f ∘ g^{-1} が Fin.t m → Fin.t m の単射 → 全射を pigeonhole で示す。 *)
Lemma inj_hom_surj_of_eq_order :
  forall (G H : Group) (m : nat)
    (f : carrier G -> carrier H)
    (Hf_hom : forall x y, f (op G x y) = op H (f x) (f y))
    (Hf_inj : forall x y, f x = f y -> x = y)
    (HordG : GroupOrder G m)
    (HordH : GroupOrder H m),
    forall y : carrier H, exists x : carrier G, f x = y.
Proof.
  intros G H m f Hf_hom Hf_inj [gG [HgG_inj HgG_surj]] [gH [HgH_inj HgH_surj]] y.
  set (phi := fun i : Fin.t m =>
    let x := @epsilon (carrier G) (inhabits (e G)) (fun x => gG x = i) in
    gH (f x)).
  assert (Hphi_inj : forall i j : Fin.t m, phi i = phi j -> i = j).
  { intros i j Heq. unfold phi in Heq.
    set (xi := @epsilon (carrier G) (inhabits (e G)) (fun x => gG x = i)).
    set (xj := @epsilon (carrier G) (inhabits (e G)) (fun x => gG x = j)).
    assert (HgGxi : gG xi = i) by (apply epsilon_spec; exact (HgG_surj i)).
    assert (HgGxj : gG xj = j) by (apply epsilon_spec; exact (HgG_surj j)).
    assert (Hfxij : f xi = f xj) by exact (HgH_inj _ _ Heq).
    assert (Hxij : xi = xj) by exact (Hf_inj _ _ Hfxij).
    rewrite <- HgGxi, <- HgGxj, Hxij. reflexivity. }
  destruct (Fin_inj_is_surj m phi Hphi_inj (gH y)) as [i Hi].
  unfold phi in Hi.
  set (xi := @epsilon (carrier G) (inhabits (e G)) (fun x => gG x = i)).
  assert (HgGxi : gG xi = i) by (apply epsilon_spec; exact (HgG_surj i)).
  assert (Hfxiy : f xi = y) by exact (HgH_inj _ _ Hi).
  exact (ex_intro _ xi Hfxiy).
Qed.

(** ===== Phase 1: 単位元判定 ===== *)

(** gcd(5, 2^n) = 1 (n ≥ 1):
    5 は奇数なので 2^n と互いに素。Z.gcd の性質から。 *)
Lemma five_gcd_pow2 : forall n : nat, (1 <= n)%nat ->
    Z.gcd 5 (Z.of_nat (2^n)) = 1.
Proof.
  intros n _.
  rewrite Zgcd_1_rel_prime.
  induction n as [|n' IH].
  - simpl. apply rel_prime_sym. apply rel_prime_1.
  - rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
    apply rel_prime_mult.
    + apply rel_prime_sym. apply prime_rel_prime. apply prime_2.
      intro H. destruct H as [k Hk]. lia.
    + destruct n' as [|n''].
      * simpl. apply rel_prime_sym. apply rel_prime_1.
      * apply IH.
Qed.

(** gcd(2^n - 1, 2^n) = 1 (n ≥ 2):
    2^n - 1 は奇数なので 2^n と互いに素。 *)
Lemma neg_one_gcd_pow2 : forall n : nat, (2 <= n)%nat ->
    Z.gcd (Z.of_nat (2^n) - 1) (Z.of_nat (2^n)) = 1.
Proof.
  intros n Hn.
  rewrite Zgcd_1_rel_prime.
  unfold rel_prime.
  apply Zis_gcd_intro; try apply Z.divide_1_l.
  intros x Hx1 Hx2.
  replace 1 with (Z.of_nat (2^n) - (Z.of_nat (2^n) - 1)) by lia.
  exact (Z.divide_sub_r _ _ _ Hx2 Hx1).
Qed.

(** 5^s ≡ 1 (mod 4) (nat 冪):
    帰納法。5 ≡ 1 (mod 4) なので 5^s ≡ 1^s = 1 (mod 4)。 *)
Lemma five_pow_mod_four : forall s : nat,
    (5 : Z) ^ (Z.of_nat s) mod 4 = 1.
Proof.
  induction s as [|s' IH].
  - simpl. reflexivity.
  - rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    rewrite Z.mul_mod by lia. rewrite IH.
    compute. reflexivity.
Qed.

(** ===== Phase 2: 鍵合同式 ===== *)


(** 5^(2^k) ≡ 1 + 2^(k+2) (mod 2^(k+3)) — 鍵補題:
    k に関する帰納法。
    - k=0: 5^1 = 5 = 1+4, 8 | (5-1-4) = 8 | 0。✓
    - k→k+1: 5^(2^(k+1)) = (5^(2^k))^2。
      IH より 5^(2^k) = 1+2^(k+2)+q*2^(k+3)。
      2乗して 2^(k+4) | ((5^(2^k))^2 - 1 - 2^(k+3)) を示す。 *)
Lemma five_pow_two_k_congr : forall k : nat,
    ((2:Z)^(Z.of_nat k + 3) | (5:Z)^(Z.of_nat (Nat.pow 2 k)) - 1 - (2:Z)^(Z.of_nat k + 2)).
Proof.
  induction k as [|k' IH].
  - simpl. exists 0. lia.
  - set (A := (5:Z)^(Z.of_nat (Nat.pow 2 k'))).
    assert (Hpow : (5:Z)^(Z.of_nat (Nat.pow 2 (S k'))) = A ^ 2).
    { unfold A. rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
      rewrite Z.mul_comm.
      rewrite Z.pow_mul_r; [reflexivity | apply Nat2Z.is_nonneg | lia]. }
    rewrite Hpow.
    replace (Z.of_nat (S k') + 3) with (Z.of_nat k' + 4) by (rewrite Nat2Z.inj_succ; lia).
    replace (Z.of_nat (S k') + 2) with (Z.of_nat k' + 3) by (rewrite Nat2Z.inj_succ; lia).
    destruct IH as [q Hq].
    assert (HA : A = 1 + (2:Z)^(Z.of_nat k' + 2) + q * (2:Z)^(Z.of_nat k' + 3)) by lia.
    set (y := (2:Z)^(Z.of_nat k')).
    assert (Hy2 : (2:Z)^(Z.of_nat k' + 2) = 4 * y) by (unfold y; rewrite Z.pow_add_r by lia; lia).
    assert (Hy3 : (2:Z)^(Z.of_nat k' + 3) = 8 * y) by (unfold y; rewrite Z.pow_add_r by lia; lia).
    assert (Hy4 : (2:Z)^(Z.of_nat k' + 4) = 16 * y) by (unfold y; rewrite Z.pow_add_r by lia; lia).
    assert (HAs : A = 1 + 4 * y + 8 * q * y) by (rewrite HA, Hy2, Hy3; lia).
    exists (q + (1 + 2 * q)^2 * y).
    rewrite Hy4, Hy3, HAs. ring.
Qed.

(** 5^(2^k * s) ≡ 1 + s * 2^(k+2) (mod 2^(k+3)):
    five_pow_two_k_congr の k に関する帰納法を s に拡張。 *)
Lemma five_pow_2k_s_congr : forall (k s : nat),
    ((2:Z)^(Z.of_nat k + 3) |
    (5:Z)^(Z.of_nat (Nat.pow 2 k * s)) - 1 - (Z.of_nat s) * (2:Z)^(Z.of_nat k + 2)).
Proof.
  intros k s. induction s as [|s' IH].
  - rewrite Nat.mul_0_r. simpl. exists 0. lia.
  - rewrite Nat.mul_succ_r, Nat2Z.inj_add.
    rewrite (Z.pow_add_r 5 (Z.of_nat (Nat.pow 2 k * s')) (Z.of_nat (Nat.pow 2 k))
               (Nat2Z.is_nonneg _) (Nat2Z.is_nonneg _)).
    rewrite Nat2Z.inj_succ.
    set (A := (5:Z)^(Z.of_nat (Nat.pow 2 k * s'))).
    set (B := (5:Z)^(Z.of_nat (Nat.pow 2 k))).
    destruct IH as [q1 Hq1].
    destruct (five_pow_two_k_congr k) as [q2 Hq2].
    assert (HA : A = 1 + Z.of_nat s' * (2:Z)^(Z.of_nat k + 2) + q1 * (2:Z)^(Z.of_nat k + 3)) by lia.
    assert (HB : B = 1 + (2:Z)^(Z.of_nat k + 2) + q2 * (2:Z)^(Z.of_nat k + 3)) by lia.
    set (y := (2:Z)^(Z.of_nat k)).
    assert (Hy2 : (2:Z)^(Z.of_nat k + 2) = 4 * y) by (unfold y; rewrite Z.pow_add_r by lia; lia).
    assert (Hy3 : (2:Z)^(Z.of_nat k + 3) = 8 * y) by (unfold y; rewrite Z.pow_add_r by lia; lia).
    assert (HAs : A = 1 + Z.of_nat s' * 4 * y + q1 * 8 * y) by (rewrite HA, Hy2, Hy3; lia).
    assert (HBs : B = 1 + 4 * y + q2 * 8 * y) by (rewrite HB, Hy2, Hy3; lia).
    exists (2 * Z.of_nat s' * y + 4 * q1 * y + A * q2 + q1).
    rewrite Hy2, Hy3, HAs, HBs. ring.
Qed.

(** ===== Phase 3: 5 の位数 ===== *)

(** 5^(2^(n-2)) ≡ 1 (mod 2^n) (n ≥ 2):
    five_pow_two_k_congr を k = n-2 で適用すると
    2^n | (5^(2^(n-2)) - 1 - 2^(n-2+2)) = 2^n | (5^(2^(n-2)) - 1 - 2^n)。
    よって 5^(2^(n-2)) ≡ 1 + 2^n ≡ 1 (mod 2^n)。 *)
Lemma five_pow_pow2_nm2_one : forall n : nat, (2 <= n)%nat ->
    (Z.of_nat (Nat.pow 2 n) | (5:Z)^(Z.of_nat (Nat.pow 2 (n-2))) - 1).
Proof.
  intros n Hn.
  set (k := (n - 2)%nat).
  assert (Hk2 : Z.of_nat k + 2 = Z.of_nat n).
  { unfold k. rewrite Nat2Z.inj_sub by lia. lia. }
  assert (Hk3 : Z.of_nat k + 3 = Z.of_nat n + 1).
  { unfold k. rewrite Nat2Z.inj_sub by lia. lia. }
  assert (Hkn2 : Nat.pow 2 k = Nat.pow 2 (n - 2)) by (unfold k; reflexivity).
  pose proof (five_pow_two_k_congr k) as H.
  rewrite Hk2, Hk3 in H.
  destruct H as [q Hq].
  assert (H2n : (2:Z)^(Z.of_nat n) = Z.of_nat (Nat.pow 2 n)).
  { rewrite Nat2Z.inj_pow. simpl Z.of_nat at 2. reflexivity. }
  assert (H2n1 : (2:Z)^(Z.of_nat n + 1) = 2 * Z.of_nat (Nat.pow 2 n)).
  { rewrite Z.pow_add_r by lia. rewrite H2n. ring. }
  rewrite H2n, H2n1 in Hq.
  exists (2 * q + 1). nia.
Qed.

(** 自然数の 2 進分解: s > 0 ならば s = 2^k * t で t 奇数となる k, t が存在する。 *)
Lemma nat_pow2_odd_decomp : forall s : nat, (0 < s)%nat ->
    exists k t : nat, (s = Nat.pow 2 k * t)%nat /\ Nat.Odd t /\ (k < Nat.log2 s + 1)%nat.
Proof.
  intro s. apply (lt_wf_ind s). clear s.
  intros s IH Hs.
  destruct (Nat.Even_or_Odd s) as [[s' Hs'] | Hs_odd].
  - assert (Hs'pos : (0 < s')%nat) by lia.
    assert (Hs'lt : (s' < s)%nat) by lia.
    destruct (IH s' Hs'lt Hs'pos) as [k [t [Hst [Hodd Hlog]]]].
    exists (k+1)%nat, t. split.
    + rewrite Nat.pow_add_r. simpl. lia.
    + split. exact Hodd.
      rewrite Hs'. rewrite Nat.log2_double by lia. lia.
  - exists 0%nat, s. simpl. split. lia. split. exact Hs_odd. lia.
Qed.

(** s * 2^r が 2^(r+1) で割り切れない (s 奇数):
    s = 2j+1 より s * 2^r = j*2^(r+1) + 2^r。2^(r+1) ∤ 2^r。 *)
Lemma pow2_times2 : forall r : nat,
    (2:Z)^(Z.of_nat r + 1) = 2 * (2:Z)^(Z.of_nat r).
Proof. intro r. rewrite Z.pow_add_r by lia. ring. Qed.

Lemma odd_mul_pow2_not_zero_mod : forall (r : nat) (s : nat),
    Nat.Odd s ->
    (Z.of_nat s) * (2:Z)^(Z.of_nat r) mod (2:Z)^(Z.of_nat r + 1) <> 0.
Proof.
  intros r s [m Hm]. subst s.
  assert (Hrpos : 0 < (2:Z)^(Z.of_nat r)) by (apply Z.pow_pos_nonneg; lia).
  rewrite pow2_times2.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
  simpl Z.of_nat at 1 3.
  generalize ((2:Z)^(Z.of_nat r)) Hrpos. intros y Hy.
  replace ((2 * Z.of_nat m + 1) * y) with (y + Z.of_nat m * (2 * y)) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(** 0 < s < 2^(n-2) ならば 5^s ≢ 1 (mod 2^n) (n ≥ 3):
    s の 2 進分解 s = 2^k * t (t 奇数, k < n-2) を取る。
    five_pow_2k_s_congr より 5^s ≡ 1 + t*2^(k+2) (mod 2^(k+3))。
    t が奇数なので t*2^(k+2) ≢ 0 (mod 2^(k+3))。
    k+3 ≤ n なので 5^s ≢ 1 (mod 2^n)。 *)
Lemma five_pow_not_one_before : forall (n s : nat),
    (3 <= n)%nat -> (0 < s)%nat -> (s < 2^(n-2))%nat ->
    ~ (Z.of_nat (Nat.pow 2 n) | (5:Z)^(Z.of_nat s) - 1).
Proof.
  intros n s Hn Hs Hslt.
  destruct (nat_pow2_odd_decomp s Hs) as [k [t [Hst [Hodd Hlog]]]].
  assert (Hkn2 : (k < n - 2)%nat).
  { assert (H2k : (Nat.pow 2 k <= s)%nat).
    { rewrite Hst. apply Nat.le_mul_r. destruct Hodd as [m Hm]. lia. }
    apply (Nat.pow_lt_mono_r_iff 2 k (n-2)%nat); lia. }
  assert (Hkn : (k + 3 <= n)%nat) by lia.
  destruct (five_pow_2k_s_congr k t) as [q Hq].
  intros [r' Hr'].
  assert (H5s : (5:Z)^(Z.of_nat s) = (5:Z)^(Z.of_nat (Nat.pow 2 k * t))) by
    (rewrite Hst; reflexivity).
  rewrite H5s in Hr'.
  assert (Hval : (5:Z)^(Z.of_nat (Nat.pow 2 k * t)) - 1 =
    Z.of_nat t * (2:Z)^(Z.of_nat k + 2) + q * (2:Z)^(Z.of_nat k + 3)) by lia.
  assert (H2n_eq : Z.of_nat (Nat.pow 2 n) =
      (2:Z)^(Z.of_nat k + 3) * (2:Z)^(Z.of_nat n - (Z.of_nat k + 3))).
  { rewrite Nat2Z.inj_pow. simpl Z.of_nat at 2.
    rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (H3t : ((2:Z)^(Z.of_nat k + 3) | Z.of_nat t * (2:Z)^(Z.of_nat k + 2))).
  { exists (r' * (2:Z)^(Z.of_nat n - (Z.of_nat k + 3)) - q).
    rewrite H2n_eq in Hr'. lia. }
  assert (H2t : ((2:Z) | Z.of_nat t)).
  { destruct H3t as [r Hr].
    assert (Hpow : (2:Z)^(Z.of_nat k + 3) = 2 * (2:Z)^(Z.of_nat k + 2)).
    { replace (Z.of_nat k + 3) with (Z.succ (Z.of_nat k + 2)) by lia.
      rewrite Z.pow_succ_r by lia. ring. }
    assert (Hpow2 : 0 < (2:Z)^(Z.of_nat k+2)) by (apply Z.pow_pos_nonneg; lia).
    rewrite Hpow in Hr.
    exists r. nia. }
  destruct Hodd as [m Hm]. subst t.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul in H2t. simpl Z.of_nat at 1 in H2t.
  destruct H2t as [j Hj]. lia.
Qed.

(** ===== Phase 4: -1 の位数 ===== *)

(** (2^n - 1)^2 ≡ 1 (mod 2^n) (n ≥ 2):
    (2^n-1)^2 = 2^(2n) - 2^(n+1) + 1 = 1 + 2^n*(2^n - 2) ≡ 1 (mod 2^n)。 *)
Lemma neg_one_sq_one_pow2 : forall n : nat, (2 <= n)%nat ->
    (Z.of_nat (Nat.pow 2 n) | (Z.of_nat (Nat.pow 2 n) - 1)^2 - 1).
Proof.
  intros n Hn.
  exists (Z.of_nat (Nat.pow 2 n) - 2). ring.
Qed.

(** 2^n - 1 ≢ 1 (mod 2^n) (n ≥ 2):
    2^n - 1 - 1 = 2^n - 2 は 2^n で割り切れない (0 < 2 < 2^n)。 *)
Lemma neg_one_ne_one_pow2 : forall n : nat, (2 <= n)%nat ->
    (Z.of_nat (Nat.pow 2 n) - 1) mod (Z.of_nat (Nat.pow 2 n)) <> 1.
Proof.
  intros n Hn.
  assert (H2n : (4 <= Nat.pow 2 n)%nat) by
    (change 4%nat with (Nat.pow 2 2); apply Nat.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia.
  lia.
Qed.

(** ===== Phase 5: 補助補題 ===== *)

(** べき乗の mod 周期性: b^M ≡ 1 (mod N) ならば b^a mod N = b^(a mod M) mod N。
    証明: a = M*q + r として b^a = (b^M)^q * b^r。
    (b^M)^q ≡ 1^q ≡ 1 (mod N) なので b^a ≡ b^r ≡ b^(a mod M) (mod N)。 *)
Lemma Zpow_mod_period_nat : forall (b N M : Z) (a : nat),
    1 < N -> 0 < M ->
    b ^ M mod N = 1 ->
    b ^ Z.of_nat a mod N = b ^ (Z.of_nat a mod M) mod N.
Proof.
  intros b N M a HN HM Hperiod.
  set (q := Z.of_nat a / M).
  set (r := Z.of_nat a mod M).
  assert (Hq : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  assert (HM0 : 0 <= M) by lia.
  assert (Hr : 0 <= r < M) by (unfold r; apply Z.mod_pos_bound; lia).
  assert (Hdiv : Z.of_nat a = M * q + r).
  { unfold q, r. pose proof (Z.div_mod (Z.of_nat a) M ltac:(lia)) as H. lia. }
  rewrite Hdiv. rewrite Z.pow_add_r by lia.
  rewrite (Z.pow_mul_r b M q HM0 Hq).
  assert (Hbmq : (b ^ M) ^ q mod N = 1).
  { rewrite <- Z.mod_pow_l. rewrite Hperiod.
    rewrite (Z.pow_1_l q Hq). apply Z.mod_1_l. lia. }
  rewrite Z.mul_mod by lia.
  rewrite Hbmq. rewrite Z.mul_1_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(** 除算の合同式変換: B | A - 1 かつ 1 < B ならば A mod B = 1。 *)
Lemma dvd_to_one_mod : forall (A B : Z), 1 < B -> ((B | A - 1)) ->
    A mod B = 1.
Proof.
  intros A B HB [q Hq].
  assert (Heq : A = 1 + q * B) by lia.
  rewrite Heq. rewrite Z.mod_add by lia. apply Z.mod_1_l. lia.
Qed.

(** 5^a mod 2^n は a mod 2^(n-2) のみに依存する (n ≥ 2):
    five_pow_pow2_nm2_one より 5^(2^(n-2)) ≡ 1 (mod 2^n)、
    Zpow_mod_period_nat より周期 2^(n-2) を持つ。 *)
Lemma five_pow_period_mod : forall (n a : nat), (2 <= n)%nat ->
    ((Z.of_nat (Nat.pow 2 n)) | (5:Z)^(Z.of_nat (Nat.pow 2 (n-2))) - 1) ->
    (5:Z)^(Z.of_nat a) mod Z.of_nat (Nat.pow 2 n) =
    (5:Z)^(Z.of_nat a mod Z.of_nat (Nat.pow 2 (n-2))) mod Z.of_nat (Nat.pow 2 n).
Proof.
  intros n a Hn Hdvd.
  assert (HN : 1 < Z.of_nat (Nat.pow 2 n)).
  { assert (H4 : (4 <= Nat.pow 2 n)%nat)
      by (change (4%nat) with (Nat.pow 2 2); apply Nat.pow_le_mono_r; lia). lia. }
  assert (HM : 0 < Z.of_nat (Nat.pow 2 (n-2))).
  { assert (H1 : (1 <= Nat.pow 2 (n-2))%nat)
      by (apply (Nat.le_trans _ (Nat.pow 2 0) _); [simpl; lia | apply Nat.pow_le_mono_r; lia]).
    lia. }
  apply Zpow_mod_period_nat; [lia | lia |].
  apply dvd_to_one_mod; [lia | exact Hdvd].
Qed.

(** (2^n - 1)^b mod 2^n は b mod 2 のみに依存する (n ≥ 2):
    neg_one_sq_one_pow2 より (2^n-1)^2 ≡ 1 (mod 2^n)、
    Zpow_mod_period_nat より周期 2 を持つ。 *)
Lemma neg_one_period_mod : forall (n b : nat), (2 <= n)%nat ->
    ((Z.of_nat (Nat.pow 2 n)) | (Z.of_nat (Nat.pow 2 n) - 1)^2 - 1) ->
    (Z.of_nat (Nat.pow 2 n) - 1)^(Z.of_nat b) mod Z.of_nat (Nat.pow 2 n) =
    (Z.of_nat (Nat.pow 2 n) - 1)^(Z.of_nat b mod 2) mod Z.of_nat (Nat.pow 2 n).
Proof.
  intros n b Hn Hdvd.
  set (N := Z.of_nat (Nat.pow 2 n)).
  assert (HN : 1 < N).
  { unfold N. assert (H4 : (4 <= Nat.pow 2 n)%nat)
      by (change (4%nat) with (Nat.pow 2 2); apply Nat.pow_le_mono_r; lia). lia. }
  apply (Zpow_mod_period_nat (N - 1) N 2); [lia | lia |].
  apply dvd_to_one_mod; [lia | exact Hdvd].
Qed.

(** 群同型の対称性: G ≅ H ならば H ≅ G。
    証明: f : G → H が全単射準同型ならば
    g := epsilon の逆写像 f^{-1} : H → G も全単射準同型。 *)
Lemma GroupIsomorphic_symm : forall G H : Group, G ≅ H -> H ≅ G.
Proof.
  intros G H [f [Hf_hom [Hf_inj Hf_surj]]].
  pose (g := fun y : carrier H =>
    @epsilon (carrier G) (inhabits (e G)) (fun x => f x = y)).
  exists g.
  assert (Hfg : forall y : carrier H, f (g y) = y).
  { intro y. unfold g. apply epsilon_spec. exact (Hf_surj y). }
  split; [| split].
  - intros y1 y2.
    apply Hf_inj.
    unfold g at 1.
    rewrite (epsilon_spec (inhabits (e G)) (fun x => f x = op H y1 y2)
               (Hf_surj (op H y1 y2))).
    rewrite Hf_hom. rewrite (Hfg y1). rewrite (Hfg y2). reflexivity.
  - intros y1 y2 Heq.
    assert (H1 : f (g y1) = y1) by exact (Hfg y1).
    assert (H2 : f (g y2) = y2) by exact (Hfg y2).
    rewrite <- H1, <- H2, Heq. reflexivity.
  - intro x. exists (f x).
    apply Hf_inj. rewrite Hfg. reflexivity.
Qed.

(** ===== Phase 5: 同型写像の構成と主定理 ===== *)

(** 算術補題: 2^(n-2) * 2 = 2^(n-1) (n ≥ 2). *)
Lemma pow2_nm2_times2 : forall n : nat, (2 <= n)%nat ->
    (Nat.pow 2 (n-2) * 2 = Nat.pow 2 (n-1))%nat.
Proof.
  intros n Hn.
  replace (n-1)%nat with (S (n-2))%nat by lia.
  rewrite Nat.pow_succ_r'. lia.
Qed.

(** Zpow_mod_period の整数冪版:
    b^M mod N = 1 かつ 0 ≤ a ならば b^a mod N = b^(a mod M) mod N。
    証明: a = Z.of_nat (Z.to_nat a) に変換して Zpow_mod_period_nat を適用。 *)
Lemma Zpow_mod_period_Z : forall (b N M a : Z),
    1 < N -> 0 < M -> 0 <= a ->
    b ^ M mod N = 1 ->
    b ^ a mod N = b ^ (a mod M) mod N.
Proof.
  intros b N M a HN HM Ha Hperiod.
  assert (Heq : a = Z.of_nat (Z.to_nat a)).
  { symmetry. apply Z2Nat.id. exact Ha. }
  rewrite Heq.
  apply Zpow_mod_period_nat; [exact HN | exact HM | exact Hperiod].
Qed.

(** 5^a ≡ 5^a' (mod 2^n) かつ 0 ≤ a, a' < 2^(n-2) ならば a = a' (n ≥ 2):
    n = 2: a, a' ∈ [0, 1) なので a = a' = 0。
    n ≥ 3: a ≠ a' なら N | 5^|a-a'| - 1 が言えて five_pow_not_one_before と矛盾。 *)
Lemma five_pow_inj_mod : forall (n : nat) (Hn : (2 <= n)%nat) (a a' : Z),
    0 <= a < Z.of_nat (Nat.pow 2 (n-2)) ->
    0 <= a' < Z.of_nat (Nat.pow 2 (n-2)) ->
    (5:Z)^a mod Z.of_nat (Nat.pow 2 n) = (5:Z)^a' mod Z.of_nat (Nat.pow 2 n) ->
    a = a'.
Proof.
  intros n Hn a a' [Ha0 Ha1] [Ha'0 Ha'1] Heq.
  set (N := Z.of_nat (Nat.pow 2 n)).
  (* n = 2: a, a' ∈ [0, 1) *)
  destruct (Nat.le_gt_cases 3 n) as [Hn3 | Hn2].
  2: { assert (n = 2%nat) by lia. subst. simpl in Ha1, Ha'1. lia. }
  (* n ≥ 3: 三分割して a ≠ a' の場合を排除 *)
  destruct (Z.compare_spec a a') as [Heqa | Hlt | Hgt]; [exact Heqa | exfalso.. |].
  - (* a < a': N | 5^(a'-a) - 1 を導く *)
    assert (HN_dvd_diff : (N | (5:Z)^a' - (5:Z)^a)).
    { exists ((5:Z)^a' / N - (5:Z)^a / N).
      pose proof (Z.div_mod ((5:Z)^a) N ltac:(unfold N; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); lia)) as H1.
      pose proof (Z.div_mod ((5:Z)^a') N ltac:(unfold N; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); lia)) as H2.
      assert (Heq_N : (5:Z)^a mod N = (5:Z)^a' mod N) by (unfold N; exact Heq).
      rewrite Heq_N in H1. lia. }
    assert (Hfactor : (5:Z)^a' - (5:Z)^a = (5:Z)^a * ((5:Z)^(a'-a) - 1)).
    { assert (Hpow : (5:Z)^a' = (5:Z)^a * (5:Z)^(a'-a)).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      rewrite Hpow. ring. }
    assert (HN_dvd_sub1 : (N | (5:Z)^(a'-a) - 1)).
    { apply Z.gauss with ((5:Z)^a).
      - rewrite <- Hfactor. exact HN_dvd_diff.
      - rewrite Z.gcd_comm. unfold N.
        apply Z.coprime_pow_l; [lia | apply five_gcd_pow2; lia]. }
    set (s := Z.to_nat (a'-a)).
    assert (Hs_pos : (0 < s)%nat) by (unfold s; zify; lia).
    assert (Hs_lt : (s < Nat.pow 2 (n-2))%nat) by (unfold s; zify; lia).
    assert (Hconv : (5:Z)^(a'-a) = (5:Z)^(Z.of_nat s)).
    { unfold s. rewrite Z2Nat.id; [reflexivity | lia]. }
    rewrite Hconv in HN_dvd_sub1.
    exact (five_pow_not_one_before n s Hn3 Hs_pos Hs_lt HN_dvd_sub1).
  - (* a > a': 対称 *)
    exfalso.
    assert (HN_dvd_diff : (N | (5:Z)^a - (5:Z)^a')).
    { exists ((5:Z)^a / N - (5:Z)^a' / N).
      pose proof (Z.div_mod ((5:Z)^a) N ltac:(unfold N; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); lia)) as H1.
      pose proof (Z.div_mod ((5:Z)^a') N ltac:(unfold N; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); lia)) as H2.
      assert (Heq_N : (5:Z)^a mod N = (5:Z)^a' mod N) by (unfold N; exact Heq).
      rewrite <- Heq_N in H2. lia. }
    assert (Hfactor : (5:Z)^a - (5:Z)^a' = (5:Z)^a' * ((5:Z)^(a-a') - 1)).
    { assert (Hpow : (5:Z)^a = (5:Z)^a' * (5:Z)^(a-a')).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      rewrite Hpow. ring. }
    assert (HN_dvd_sub1 : (N | (5:Z)^(a-a') - 1)).
    { apply Z.gauss with ((5:Z)^a').
      - rewrite <- Hfactor. exact HN_dvd_diff.
      - rewrite Z.gcd_comm. unfold N.
        apply Z.coprime_pow_l; [lia | apply five_gcd_pow2; lia]. }
    set (s := Z.to_nat (a-a')).
    assert (Hs_pos : (0 < s)%nat) by (unfold s; zify; lia).
    assert (Hs_lt : (s < Nat.pow 2 (n-2))%nat) by (unfold s; zify; lia).
    assert (Hconv : (5:Z)^(a-a') = (5:Z)^(Z.of_nat s)).
    { unfold s. rewrite Z2Nat.id; [reflexivity | lia]. }
    rewrite Hconv in HN_dvd_sub1.
    exact (five_pow_not_one_before n s Hn3 Hs_pos Hs_lt HN_dvd_sub1).
Qed.

(** (Z/2^nZ)* の構造定理: (Z/2^nZ)* ≅ Z/2^(n-2)Z × Z/2Z  (n ≥ 2).

    同型写像 φ : Z/2^(n-2)Z × Z/2Z → (Z/2^nZ)*
      φ(a, b) = 5^a * (2^n - 1)^b  mod 2^n

    準同型性: 指数の加算 ↔ 乗算のモジュラー。
    単射性:
      - b ≠ b': 5^a ≡ 5^a' * (2^n-1)^(b'-b) (mod 2^n)。mod 4 で 1 ≡ 3 の矛盾。
      - b = b': 5^a ≡ 5^a' → five_pow_inj_mod より a = a'。
    全射性: GroupOrder の等位数から単射 → 全射。 *)
Theorem znz_units_pow2_structure :
  forall (n : nat) (Hn : (2 <= n)%nat)
         (H2n : (1 < Nat.pow 2 n)%nat) (Hn2 : (0 < Nat.pow 2 (n-2))%nat),
    znz_units_group (Nat.pow 2 n) H2n ≅
    znz_group (Nat.pow 2 (n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1).
Proof.
  intros n Hn H2n Hn2.
  apply GroupIsomorphic_symm.
  (* 基本的な定数と事実の設定 *)
  set (N := Z.of_nat (Nat.pow 2 n)).
  set (M := Z.of_nat (Nat.pow 2 (n-2))).
  assert (HNpos : 0 < N) by (unfold N; lia).
  assert (HN1 : 1 < N) by (unfold N; lia).
  assert (HMpos : 0 < M) by (unfold M; lia).
  assert (Hn_pos : (0 < Nat.pow 2 n)%nat) by lia.
  (* 5 の周期 M: 5^M ≡ 1 (mod N) *)
  assert (Hper5 : (5:Z)^M mod N = 1).
  { apply dvd_to_one_mod; [exact HN1|].
    unfold M, N. apply five_pow_pow2_nm2_one. exact Hn. }
  (* (N-1) の周期 2: (N-1)^2 ≡ 1 (mod N) *)
  assert (Hper_neg1 : (N-1)^(2:Z) mod N = 1).
  { apply dvd_to_one_mod; [exact HN1|].
    unfold N. apply neg_one_sq_one_pow2. exact Hn. }
  (* gcd(5^a, N) = 1 *)
  assert (Hgcd5 : forall a : Z, 0 <= a -> Z.gcd ((5:Z)^a) N = 1).
  { intros a Ha. unfold N.
    apply Z.coprime_pow_l; [exact Ha | apply five_gcd_pow2; lia]. }
  (* gcd((N-1)^b, N) = 1 *)
  assert (Hgcd_neg1 : forall b : Z, 0 <= b -> Z.gcd ((N-1)^b) N = 1).
  { intros b Hb.
    apply Z.coprime_pow_l; [exact Hb |].
    unfold N. apply neg_one_gcd_pow2. exact Hn. }
  (* 4 | N: n >= 2 なので 2^n = 4 * 2^(n-2) *)
  assert (H4N : ((4:Z) | N)).
  { unfold N.
    exists (Z.of_nat (Nat.pow 2 (n-2))).
    assert (H : (Nat.pow 2 n = 4 * Nat.pow 2 (n-2))%nat).
    { change (4%nat) with (Nat.pow 2 2).
      rewrite <- Nat.pow_add_r. f_equal. lia. }
    apply (f_equal Z.of_nat) in H.
    rewrite Nat2Z.inj_mul in H.
    lia. }
  (* (N-1) mod 4 = 3: N ≡ 0 (mod 4) なので N-1 ≡ -1 ≡ 3 (mod 4) *)
  assert (HN1_mod4 : (N-1) mod 4 = 3).
  { destruct H4N as [q Hq].
    replace (N-1) with (-1 + q*4) by lia.
    rewrite Z.mod_add by lia.
    compute. reflexivity. }
  (* 同型写像 φ(a, b) = 5^a * (N-1)^b mod N の定義 *)
  set (phi :=
    fun pair : carrier (znz_group (Nat.pow 2 (n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1)) =>
    let a := proj1_sig (fst pair) in
    let b := proj1_sig (snd pair) in
    exist (fun x : Z => 0 <= x < N /\ Z.gcd x N = 1)
      ((5:Z)^a * (N - 1)^b mod N)
      (conj
        (Z.mod_pos_bound _ N HNpos)
        (eq_trans
          (znz_gcd_mod_eq (Nat.pow 2 n) Hn_pos ((5:Z)^a * (N-1)^b))
          (znz_gcd_mul_coprime (Nat.pow 2 n) ((5:Z)^a) ((N-1)^b)
            (Hgcd5 a (proj1 (proj2_sig (fst pair))))
            (Hgcd_neg1 b (proj1 (proj2_sig (snd pair)))))))).
  (* 準同型性の事前証明 *)
  assert (Hhom : forall p1 p2,
      phi (op (znz_group (Nat.pow 2 (n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1)) p1 p2) =
      op (znz_units_group (Nat.pow 2 n) H2n) (phi p1) (phi p2)).
  { intros [[a1 Ha1] [b1 Hb1]] [[a2 Ha2] [b2 Hb2]].
    unfold phi. apply sig_eq. simpl.
    fold N. fold M.
    (* Goal: 5^((a1+a2) mod M) * (N-1)^((b1+b2) mod 2) mod N
           = 5^a1*(N-1)^b1 mod N * (5^a2*(N-1)^b2 mod N) mod N *)
    rewrite Z.mul_mod at 1 by lia.
    rewrite <- (Zpow_mod_period_Z 5 N M (a1+a2) HN1 HMpos ltac:(lia) Hper5).
    rewrite <- (Zpow_mod_period_Z (N-1) N 2 (b1+b2) HN1 ltac:(lia) ltac:(lia) Hper_neg1).
    rewrite <- Z.mul_mod by lia.
    rewrite <- Z.mul_mod by lia.
    f_equal.
    rewrite (Z.pow_add_r 5 a1 a2 (proj1 Ha1) (proj1 Ha2)).
    rewrite (Z.pow_add_r (N-1) b1 b2 (proj1 Hb1) (proj1 Hb2)).
    ring. }
  (* 単射性の事前証明 *)
  assert (Hinj : forall p1 p2,
      phi p1 = phi p2 -> p1 = p2).
  { intros [[a1 Ha1] [b1 Hb1]] [[a2 Ha2] [b2 Hb2]] Heq.
    unfold phi in Heq. injection Heq as Heq.
    (* Heq : (5:Z)^a1 * (N-1)^b1 mod N = (5:Z)^a2 * (N-1)^b2 mod N *)
    (* N | 5^a1*(N-1)^b1 - 5^a2*(N-1)^b2 を導出 *)
    assert (HN_dvd : (N | (5:Z)^a1*(N-1)^b1 - (5:Z)^a2*(N-1)^b2)).
    { exists ((5:Z)^a1*(N-1)^b1 / N - (5:Z)^a2*(N-1)^b2 / N).
      pose proof (Z.div_mod ((5:Z)^a1*(N-1)^b1) N ltac:(lia)) as H1.
      pose proof (Z.div_mod ((5:Z)^a2*(N-1)^b2) N ltac:(lia)) as H2.
      lia. }
    (* 4 | diff *)
    assert (H4_dvd : ((4:Z) | (5:Z)^a1*(N-1)^b1 - (5:Z)^a2*(N-1)^b2)).
    { destruct H4N as [kN HkN].
      destruct HN_dvd as [kD HkD].
      exists (kN * kD). lia. }
    (* mod 4 の等式 *)
    assert (Hmod4 : (5:Z)^a1*(N-1)^b1 mod 4 = (5:Z)^a2*(N-1)^b2 mod 4).
    { destruct H4_dvd as [k Hk].
      assert (H : (5:Z)^a1*(N-1)^b1 = (5:Z)^a2*(N-1)^b2 + k*4) by lia.
      rewrite H. rewrite Z.mod_add by lia. reflexivity. }
    (* b1 = b2 の証明: b1 ≠ b2 なら mod 4 で矛盾 *)
    assert (Hbb : b1 = b2).
    { assert (Hb1_range : b1 = 0 \/ b1 = 1) by lia.
      assert (Hb2_range : b2 = 0 \/ b2 = 1) by lia.
      destruct Hb1_range as [Hb10|Hb11]; destruct Hb2_range as [Hb20|Hb21]; try lia.
      - (* b1=0, b2=1: 5^a1 mod 4 = 1 vs 5^a2*(N-1) mod 4 = 3 で矛盾 *)
        exfalso. subst b1. subst b2.
        rewrite Z.pow_0_r, Z.mul_1_r in Hmod4.
        rewrite Z.pow_1_r in Hmod4.
        assert (H5a1 : (5:Z)^a1 mod 4 = 1).
        { replace a1 with (Z.of_nat (Z.to_nat a1))
            by (apply Z2Nat.id; exact (proj1 Ha1)).
          apply five_pow_mod_four. }
        assert (H5a2N1 : (5:Z)^a2 * (N-1) mod 4 = 3).
        { rewrite Z.mul_mod by lia.
          replace a2 with (Z.of_nat (Z.to_nat a2))
            by (apply Z2Nat.id; exact (proj1 Ha2)).
          rewrite five_pow_mod_four. rewrite HN1_mod4.
          compute. reflexivity. }
        lia.
      - (* b1=1, b2=0: 5^a1*(N-1) mod 4 = 3 vs 5^a2 mod 4 = 1 で矛盾 *)
        exfalso. subst b1. subst b2.
        rewrite Z.pow_1_r, Z.pow_0_r, Z.mul_1_r in Hmod4.
        assert (H5a1N1 : (5:Z)^a1 * (N-1) mod 4 = 3).
        { rewrite Z.mul_mod by lia.
          replace a1 with (Z.of_nat (Z.to_nat a1))
            by (apply Z2Nat.id; exact (proj1 Ha1)).
          rewrite five_pow_mod_four. rewrite HN1_mod4.
          compute. reflexivity. }
        assert (H5a2 : (5:Z)^a2 mod 4 = 1).
        { replace a2 with (Z.of_nat (Z.to_nat a2))
            by (apply Z2Nat.id; exact (proj1 Ha2)).
          apply five_pow_mod_four. }
        lia. }
    subst b2.
    (* a1 = a2 の証明 *)
    assert (Haa : a1 = a2).
    { assert (Hb1_range : b1 = 0 \/ b1 = 1) by lia.
      destruct Hb1_range as [Hb10|Hb11].
      - (* b1=0: 5^a1 ≡ 5^a2 (mod N) → five_pow_inj_mod *)
        subst b1. rewrite !Z.pow_0_r, !Z.mul_1_r in Heq.
        unfold N in Heq.
        exact (five_pow_inj_mod n Hn a1 a2 Ha1 Ha2 Heq).
      - (* b1=1: Z.gauss で (N-1) を消去 → five_pow_inj_mod *)
        subst b1. rewrite Z.pow_1_r in Heq.
        assert (HN_dvd2 : (N | (5:Z)^a1*(N-1) - (5:Z)^a2*(N-1))).
        { exists ((5:Z)^a1*(N-1) / N - (5:Z)^a2*(N-1) / N).
          pose proof (Z.div_mod ((5:Z)^a1*(N-1)) N ltac:(lia)) as H1.
          pose proof (Z.div_mod ((5:Z)^a2*(N-1)) N ltac:(lia)) as H2.
          lia. }
        assert (HN_dvd5 : (N | (5:Z)^a1 - (5:Z)^a2)).
        { apply Z.gauss with (N-1).
          - replace ((5:Z)^a1*(N-1) - (5:Z)^a2*(N-1)) with
                ((N-1) * ((5:Z)^a1 - (5:Z)^a2)) in HN_dvd2 by ring.
            exact HN_dvd2.
          - rewrite Z.gcd_comm. unfold N. apply neg_one_gcd_pow2. exact Hn. }
        assert (Heq5 : (5:Z)^a1 mod N = (5:Z)^a2 mod N).
        { destruct HN_dvd5 as [k Hk].
          assert (H : (5:Z)^a1 = (5:Z)^a2 + k*N) by lia.
          rewrite H. rewrite Z.mod_add by lia. reflexivity. }
        unfold N in Heq5.
        exact (five_pow_inj_mod n Hn a1 a2 Ha1 Ha2 Heq5). }
    (* ペアの等式を証明 *)
    f_equal; apply sig_eq; simpl; [exact Haa | reflexivity]. }
  (* 全射性: GroupOrder の等位数から単射 → 全射 *)
  exists phi.
  split; [| split].
  - exact Hhom.
  - exact Hinj.
  - assert (HordG : GroupOrder
        (znz_group (Nat.pow 2 (n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1))
        (Nat.pow 2 (n-1))).
    { rewrite <- (pow2_nm2_times2 n Hn).
      apply group_order_product.
      - exact (znz_group_order_n _ Hn2).
      - exact (znz_group_order_n 2 (Nat.lt_0_succ 1)). }
    exact (inj_hom_surj_of_eq_order
      (znz_group (Nat.pow 2 (n-2)) Hn2 ×ₒ znz_group 2 (Nat.lt_0_succ 1))
      (znz_units_group (Nat.pow 2 n) H2n)
      (Nat.pow 2 (n-1))
      phi Hhom Hinj HordG (znz_units_pow2_order n Hn H2n)).
Qed.

(* ================================================================= *)
(*  (Z/p^nZ)* の構造定理と巡回性 (奇素数 p)                           *)
(*  Theorem 1: (Z/p^nZ)* ≅ Z/p^(n-1)Z × Z/(p-1)Z (p 奇素数)        *)
(*  Theorem 2: (Z/p^nZ)* は巡回群                                     *)
(* ================================================================= *)

(** GroupIsomorphic の推移律:
    G ≅ H かつ H ≅ K ならば G ≅ K。
    証明: 合成写像 k∘f : G → K が同型であることを示す。 *)
Lemma GroupIsomorphic_trans : forall G H K : Group,
    G ≅ H -> H ≅ K -> G ≅ K.
Proof.
  intros G H K [f [Hf_hom [Hf_inj Hf_surj]]] [g [Hg_hom [Hg_inj Hg_surj]]].
  exists (fun x => g (f x)).
  split; [| split].
  - intros x y. rewrite Hf_hom. rewrite Hg_hom. reflexivity.
  - intros x y Heq. apply Hf_inj. apply Hg_inj. exact Heq.
  - intro z. destruct (Hg_surj z) as [y Hy]. destruct (Hf_surj y) as [x Hx].
    exists x. rewrite Hx. exact Hy.
Qed.

(** ===== Phase 0: 算術基礎補題 ===== *)

(** 奇素数 p と n ≥ 1 のとき 1 < p^n。 *)
Lemma odd_prime_pow_gt_one : forall (p n : nat),
    (1 < p)%nat -> (1 <= n)%nat -> (1 < p^n)%nat.
Proof.
  intros p n Hp Hn.
  apply Nat.pow_gt_1; lia.
Qed.

(** (Z/p^nZ)* の位数は p^(n-1) * (p-1)。
    euler_phi (p^n) = p^(n-1) * (p-1) (euler_phi_prime_pow)、
    euler_phi_group_order より GroupOrder (znz_units_group (p^n) _) (euler_phi (p^n))。 *)
Lemma odd_prime_pow_units_order : forall (p n : nat)
    (Hp : (1 < p)%nat) (Hprime : prime (Z.of_nat p)) (Hn : (1 <= n)%nat)
    (Hpn : (1 < p^n)%nat),
    GroupOrder (znz_units_group (p^n) Hpn) (p^(n-1) * (p-1)).
Proof.
  intros p n Hp Hprime Hn Hpn.
  assert (Hord : GroupOrder (znz_units_group (p^n) Hpn) (euler_phi (p^n)))
    by apply euler_phi_group_order.
  rewrite (euler_phi_prime_pow p n Hprime Hn) in Hord.
  exact Hord.
Qed.


(** ===== Phase 1: (1+p) の位数 p^(n-1) ===== *)

(** 等比数列の和を定義する:
    geom_sum A n = A^0 + A^1 + ... + A^(n-1) = sum_{i=0}^{n-1} A^i。
    キー性質: (A-1) * geom_sum A n = A^n - 1。 *)
Fixpoint geom_sum (A : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => A ^ Z.of_nat n' + geom_sum A n'
  end.

(** geom_sum の基本性質: (A-1) * geom_sum A n = A^n - 1。 *)
Lemma geom_sum_spec : forall (A : Z) (n : nat),
    (A - 1) * geom_sum A n = A ^ Z.of_nat n - 1.
Proof.
  intros A n. induction n as [| n' IH].
  - simpl. ring.
  - simpl geom_sum. rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    lia.
Qed.

(** geom_sum の分割補題:
    geom_sum A (p * N) = geom_sum (A^N) p * geom_sum A N。
    証明: N の帰納法。 *)
Lemma geom_sum_split : forall (A : Z) (p N : nat),
    geom_sum A (p * N) = geom_sum (A ^ Z.of_nat N) p * geom_sum A N.
Proof.
  intros A p N.
  (* 補助補題: geom_sum A (k + N) = geom_sum A k + A^k * geom_sum A N *)
  assert (Hstep : forall k, geom_sum A (k + N) = geom_sum A k + A^(Z.of_nat k) * geom_sum A N).
  { intros k. induction k as [| k' IHk].
    - simpl geom_sum. rewrite Z.pow_0_r. ring.
    - (* S k' のステップ *)
      change (S k' + N)%nat with (S (k' + N)%nat).
      simpl geom_sum.
      rewrite Nat2Z.inj_succ.
      rewrite IHk.
      (* A^(k'+N) = A^k' * A^N を示す *)
      rewrite Nat2Z.inj_add.
      rewrite Z.pow_add_r by lia.
      (* A^(k'+1) = A^k' * A *)
      rewrite Z.pow_succ_r by lia.
      (* geom_sum_spec: A^N - 1 = (A-1) * geom_sum A N => A^N = 1 + (A-1)*geom_sum A N *)
      assert (HAN : A ^ Z.of_nat N = 1 + (A - 1) * geom_sum A N)
        by (pose proof (geom_sum_spec A N); lia).
      rewrite HAN. ring. }
  induction p as [| p' IH].
  - simpl. ring.
  - rewrite Nat.mul_succ_l.
    rewrite (Hstep (p' * N)%nat).
    rewrite IH.
    simpl geom_sum.
    rewrite Nat2Z.inj_mul.
    rewrite (Z.mul_comm (Z.of_nat p') (Z.of_nat N)).
    rewrite <- Z.pow_mul_r by lia.
    ring.
Qed.

(** 代数的補題: (A-1)^2 | A^i - 1 - i*(A-1)。
    証明: i の帰納法。
    - i=0: A^0 - 1 - 0*(A-1) = 0。
    - i+1: A^(i+1) - 1 - (i+1)*(A-1) = A*(A^i-1-i*(A-1)) + i*(A-1)^2。 *)
Lemma sq_dvd_pow_minus_one_linear : forall (A : Z) (i : nat),
    ((A - 1)^2 | A^(Z.of_nat i) - 1 - Z.of_nat i * (A - 1)).
Proof.
  intros A i. induction i as [| i' IH].
  - simpl. exists 0. ring.
  - rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    destruct IH as [q Hq].
    exists (A * q + Z.of_nat i').
    assert (Hpow : A ^ Z.of_nat i' = q * (A - 1)^2 + 1 + Z.of_nat i' * (A - 1)) by lia.
    rewrite Hpow. ring.
Qed.

(** p | geom_sum A p (p は A-1 を割るとき):
    各 A^i ≡ 1 (mod p) なので sum ≡ p ≡ 0 (mod p)。
    証明: (A-1) | geom_sum A p - p を帰納法で示し、
    p | A-1 と推移律で p | geom_sum A p - p を得る。 *)
Lemma geom_sum_dvd_p : forall (A : Z) (p : nat),
    (Z.of_nat p | A - 1) ->
    (Z.of_nat p | geom_sum A p).
Proof.
  intros A p Hdvd.
  (* Step 1: (A-1) | geom_sum A p - Z.of_nat p *)
  assert (H_step : (A - 1 | geom_sum A p - Z.of_nat p)).
  { clear Hdvd. induction p as [| p' IH].
    - simpl. exists 0. ring.
    - simpl geom_sum. rewrite Nat2Z.inj_succ.
      pose proof (geom_sum_spec A p') as Hspec.
      destruct IH as [q Hq].
      exists (geom_sum A p' + q).
      (* (A-1)*(G+q) = (A-1)*G + (A-1)*q = (A^p'-1)+(G-N) = A^p'+G-N-1 *)
      transitivity ((A - 1) * geom_sum A p' + q * (A - 1)).
      + rewrite Hspec. rewrite <- Hq. ring.
      + ring. }
  replace (geom_sum A p) with (geom_sum A p - Z.of_nat p + Z.of_nat p) by lia.
  apply Z.divide_add_r.
  - exact (Z.divide_trans _ (A - 1) _ Hdvd H_step).
  - exact (Z.divide_refl _).
Qed.


(** p^k | geom_sum (1+p) (p^k):
    帰納法で証明する。
    - k=0: geom_sum (1+p) 1 = 1 = (1+p)^0、p^0 = 1 | 1。
    - k+1: geom_sum_split より geom_sum (1+p) (p^(k+1)) = geom_sum ((1+p)^(p^k)) p * geom_sum (1+p) (p^k)。
      IH: p^k | geom_sum (1+p) (p^k)。
      geom_sum_dvd_p と (1+p)^(p^k) ≡ 1 (mod p) より p | geom_sum ((1+p)^(p^k)) p。
      よって p^(k+1) | 積。 *)
Lemma one_plus_p_geom_sum_pk_dvd : forall (p k : nat),
    prime (Z.of_nat p) ->
    (Z.of_nat (p^k) | geom_sum (1 + Z.of_nat p) (p^k)).
Proof.
  intros p k Hprime.
  induction k as [| k' IH].
  - simpl. exists 1. ring.
  - (* S k' case: p^(S k') = p * p^k' *)
    assert (Hpow : (p ^ S k' = p * p ^ k')%nat) by exact (Nat.pow_succ_r' p k').
    rewrite Hpow.
    rewrite (geom_sum_split (1 + Z.of_nat p) p (p^k')).
    rewrite Nat2Z.inj_mul.
    (* Z.of_nat p | geom_sum ((1+p)^(p^k')) p *)
    assert (Hdvd_p : (Z.of_nat p | geom_sum ((1 + Z.of_nat p) ^ Z.of_nat (p^k')) p)).
    { apply geom_sum_dvd_p.
      pose proof (geom_sum_spec (1 + Z.of_nat p) (p^k')) as Hspec.
      assert (HA : (1 + Z.of_nat p) - 1 = Z.of_nat p) by ring.
      rewrite HA in Hspec.
      rewrite <- Hspec.
      apply Z.divide_mul_l, Z.divide_refl. }
    (* Z.of_nat p * Z.of_nat (p^k') | G_p * G_k' *)
    destruct Hdvd_p as [x Hx]. destruct IH as [y Hy].
    exists (x * y). rewrite Hx, Hy. ring.
Qed.

(** p^(k+1) | (1+p)^(p^k) - 1 (下界):
    geom_sum_spec と one_plus_p_geom_sum_pk_dvd から直接。 *)
Lemma one_plus_p_pow_pk_dvd : forall (p k : nat),
    prime (Z.of_nat p) ->
    (Z.of_nat (p^(k+1)) | (1 + Z.of_nat p) ^ Z.of_nat (p^k) - 1).
Proof.
  intros p k Hprime.
  pose proof (geom_sum_spec (1 + Z.of_nat p) (p^k)) as Hspec.
  assert (HA : (1 + Z.of_nat p) - 1 = Z.of_nat p) by ring.
  rewrite HA in Hspec.
  assert (Hpow : (p ^ (k + 1) = p * p ^ k)%nat) by
    (rewrite Nat.add_1_r; exact (Nat.pow_succ_r' p k)).
  rewrite Hpow, Nat2Z.inj_mul, <- Hspec.
  (* Goal: Z.of_nat p * Z.of_nat (p^k) | Z.of_nat p * geom_sum (1+p) (p^k) *)
  destruct (one_plus_p_geom_sum_pk_dvd p k Hprime) as [y Hy].
  exists y. rewrite Hy. ring.
Qed.

(** 等比数列部分和のインデックス和 (0 + 1 + ... + (n-1)):
    geom_sum の二次近似に必要。 *)
Fixpoint nat_sum_below (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Z.of_nat n' + nat_sum_below n'
  end.

(** 二倍公式: 2 * nat_sum_below n = Z.of_nat n * (Z.of_nat n - 1). *)
Lemma nat_sum_below_double : forall n : nat,
    2 * nat_sum_below n = Z.of_nat n * (Z.of_nat n - 1).
Proof.
  intros n. induction n as [| n' IH].
  - simpl. ring.
  - simpl nat_sum_below. rewrite Nat2Z.inj_succ. lia.
Qed.

(** 奇素数 p に対して p | nat_sum_below p。
    2*T = p*(p-1)、gcd(2,p)=1 より p|T。 *)
Lemma nat_sum_below_dvd_odd_prime : forall p : nat,
    prime (Z.of_nat p) -> p <> 2%nat ->
    (Z.of_nat p | nat_sum_below p).
Proof.
  intros p Hprime Hodd.
  pose proof (nat_sum_below_double p) as H2T.
  assert (Hdvd2T : (Z.of_nat p | 2 * nat_sum_below p)).
  { rewrite H2T. apply Z.divide_mul_l, Z.divide_refl. }
  (* gcd(Z.of_nat p, 2) = 1 (p は奇素数なので 2 ∤ p) *)
  assert (Hcop : Z.gcd (Z.of_nat p) 2 = 1).
  { rewrite Zgcd_1_rel_prime.
    apply rel_prime_sym, prime_rel_prime.
    - exact prime_2.
    - intro Hdvd.
      destruct (prime_divisors _ Hprime _ Hdvd) as [H | [H | [H | H]]].
      + lia.
      + lia.
      + apply Hodd. lia.
      + apply prime_ge_2 in Hprime. lia. }
  exact (Z.gauss _ _ _ Hdvd2T Hcop).
Qed.

(** (A-1)^2 | geom_sum A p - Z.of_nat p - (A-1) * nat_sum_below p。
    sq_dvd_pow_minus_one_linear を各 i に適用して足し合わせる。 *)
Lemma geom_sum_sq_approx : forall (A : Z) (p : nat),
    ((A - 1)^2 | geom_sum A p - Z.of_nat p - (A - 1) * nat_sum_below p).
Proof.
  intros A p. induction p as [| p' IH].
  - simpl. exists 0. ring.
  - simpl geom_sum. simpl nat_sum_below. rewrite Nat2Z.inj_succ. unfold Z.succ.
    pose proof (sq_dvd_pow_minus_one_linear A p') as Hsq.
    (* goal = (A^p' - 1 - p'*(A-1)) + (geom_sum A p' - p' - (A-1)*T) *)
    replace (A ^ Z.of_nat p' + geom_sum A p' - (Z.of_nat p' + 1) -
             (A - 1) * (Z.of_nat p' + nat_sum_below p'))
      with ((A ^ Z.of_nat p' - 1 - Z.of_nat p' * (A - 1)) +
            (geom_sum A p' - Z.of_nat p' - (A - 1) * nat_sum_below p')) by ring.
    apply Z.divide_add_r; [exact Hsq | exact IH].
Qed.

(** geom_sum ((1+p)^(p^k)) p は p^2 で割り切れない (奇素数 p):
    A = (1+p)^(p^k) とすると A-1 = p*G_k。
    geom_sum_sq_approx より p^2 | geom_sum A p - p - (A-1)*T。
    p^2 | geom_sum A p (仮定) かつ p | (A-1)*T = p*G_k*T より p^2 | p。矛盾。 *)
Lemma geom_sum_not_dvd_p_sq : forall (p k : nat),
    prime (Z.of_nat p) ->
    (2 <= p)%nat ->
    p <> 2%nat ->
    ~ (Z.of_nat (p^2) | geom_sum ((1 + Z.of_nat p) ^ Z.of_nat (p^k)) p).
Proof.
  intros p k Hprime Hp2 Hodd Hdvd.
  set (A := (1 + Z.of_nat p) ^ Z.of_nat (p ^ k)).
  set (Gk := geom_sum (1 + Z.of_nat p) (p ^ k)).
  set (T := nat_sum_below p).
  (* A - 1 = p * Gk *)
  assert (HA1 : A - 1 = Z.of_nat p * Gk).
  { unfold A, Gk.
    pose proof (geom_sum_spec (1 + Z.of_nat p) (p^k)) as Hspec.
    assert (Hbase : (1 + Z.of_nat p) - 1 = Z.of_nat p) by ring.
    rewrite Hbase in Hspec. lia. }
  (* (A-1)^2 | geom_sum A p - p - (A-1)*T *)
  pose proof (geom_sum_sq_approx A p) as Happrox.
  (* p^2 | Z.of_nat (p^2) = Z.of_nat p ^ 2 *)
  assert (Hp2eq : Z.of_nat (p ^ 2) = Z.of_nat p ^ 2).
  { rewrite Nat2Z.inj_pow. reflexivity. }
  rewrite Hp2eq in Hdvd.
  (* p^2 | (A-1)^2 since A-1 = p*Gk *)
  assert (Hp2_A1sq : (Z.of_nat p ^ 2 | (A - 1) ^ 2)).
  { rewrite HA1. exists (Gk ^ 2). ring. }
  (* p^2 | geom_sum A p - p - (A-1)*T *)
  assert (Hp2_diff : (Z.of_nat p ^ 2 | geom_sum A p - Z.of_nat p - (A - 1) * T)).
  { exact (Z.divide_trans _ _ _ Hp2_A1sq Happrox). }
  (* p^2 | p + (A-1)*T = p*(1 + Gk*T) *)
  assert (Hp2_pGkT : (Z.of_nat p ^ 2 | Z.of_nat p * (1 + Gk * T))).
  { assert (Heq : geom_sum A p - Z.of_nat p * (1 + Gk * T) =
                  geom_sum A p - Z.of_nat p - (A - 1) * T).
    { rewrite HA1. unfold T. ring. }
    replace (Z.of_nat p * (1 + Gk * T))
      with (geom_sum A p - (geom_sum A p - Z.of_nat p * (1 + Gk * T))) by ring.
    apply Z.divide_sub_r.
    - exact Hdvd.
    - rewrite Heq. exact Hp2_diff. }
  (* p | 1 + Gk*T (cancel p from p^2 | p*(1+Gk*T)) *)
  assert (Hp_1GkT : (Z.of_nat p | 1 + Gk * T)).
  { replace (Z.of_nat p ^ 2) with (Z.of_nat p * Z.of_nat p) in Hp2_pGkT by ring.
    apply (Z.mul_divide_cancel_l _ _ (Z.of_nat p)).
    - lia.
    - exact Hp2_pGkT. }
  (* p | Gk*T (either p|Gk for k≥1, or p|T for k=0) *)
  assert (Hp_GkT : (Z.of_nat p | Gk * T)).
  { unfold T.
    destruct k as [|k'].
    - (* k=0: Gk = geom_sum (1+p) 1 = 1, T = nat_sum_below p, p|T *)
      assert (HGk0 : Gk = 1).
      { unfold Gk. cbn. ring. }
      rewrite HGk0. rewrite Z.mul_1_l.
      exact (nat_sum_below_dvd_odd_prime p Hprime Hodd).
    - (* k≥1: p^(S k') | Gk, hence p | Gk *)
      apply Z.divide_mul_l.
      apply Z.divide_trans with (m := Z.of_nat (p ^ S k')).
      + (* Z.of_nat p | Z.of_nat (p ^ S k') since p^(S k') = p * p^k' *)
        exists (Z.of_nat (p ^ k')).
        rewrite Nat.pow_succ_r', Nat2Z.inj_mul. ring.
      + exact (one_plus_p_geom_sum_pk_dvd p (S k') Hprime). }
  (* p | (1+Gk*T) - Gk*T = 1. Contradiction since p ≥ 2. *)
  assert (Hp1 : (Z.of_nat p | 1)).
  { replace 1 with (1 + Gk * T - Gk * T) by ring.
    exact (Z.divide_sub_r _ _ _ Hp_1GkT Hp_GkT). }
  destruct (Z.divide_1_r _ Hp1) as [Heq | Heq].
  - apply prime_ge_2 in Hprime. lia.
  - pose proof (Nat2Z.is_nonneg p). lia.
Qed.

(** (1+p)^(p^k) - 1 の p 進付値の上界: p^(k+2) ∤ (1+p)^(p^k) - 1。
    帰納法: k=0 は p^2∤p。帰納ステップは
    (1+p)^(p^(k+1)) - 1 = (A-1)*geom_sum A p で
    v_p(A-1) = k+1 (IH), v_p(geom_sum A p) = 1 (not_dvd_p_sq) から。 *)
Lemma one_plus_p_pow_pk_not_dvd : forall (p k : nat),
    prime (Z.of_nat p) ->
    (2 <= p)%nat ->
    p <> 2%nat ->
    ~ (Z.of_nat (p ^ (k + 2)) | (1 + Z.of_nat p) ^ Z.of_nat (p ^ k) - 1).
Proof.
  intros p k Hprime Hp2 Hodd.
  induction k as [|k' IH].
  - (* k=0: p^2 ∤ (1+p)^1 - 1 = p *)
    intro Hdvd.
    assert (Heq1 : (1 + Z.of_nat p) ^ Z.of_nat (p ^ 0) - 1 = Z.of_nat p).
    { rewrite Nat.pow_0_r. change (Z.of_nat 1) with 1. rewrite Z.pow_1_r. ring. }
    assert (Heq2 : Z.of_nat (p ^ (0 + 2)) = Z.of_nat p * Z.of_nat p).
    { simpl. rewrite Nat.mul_1_r. apply Nat2Z.inj_mul. }
    rewrite Heq1, Heq2 in Hdvd.
    (* Z.of_nat p * Z.of_nat p | Z.of_nat p → p | 1 → contradiction *)
    assert (Hp1 : (Z.of_nat p | 1)).
    { assert (Hpne : Z.of_nat p <> 0) by lia.
      assert (H : (Z.of_nat p * Z.of_nat p | Z.of_nat p * 1)).
      { rewrite Z.mul_1_r. exact Hdvd. }
      exact (proj1 (Z.mul_divide_cancel_l _ _ _ Hpne) H). }
    destruct (Z.divide_1_r _ Hp1) as [Heq | Heq].
    + apply prime_ge_2 in Hprime. lia.
    + pose proof (Nat2Z.is_nonneg p). lia.
  - (* k = S k': need p^(k'+3) ∤ (1+p)^(p^(S k')) - 1 *)
    intro Hdvd.
    (* Key factorization: (1+p)^(p^(S k')) - 1 = (A-1)*geom_sum A p
       where A = (1+p)^(p^k') *)
    assert (Hfact : ((1 + Z.of_nat p) ^ Z.of_nat (p ^ k') - 1) *
                    geom_sum ((1 + Z.of_nat p) ^ Z.of_nat (p ^ k')) p =
                    (1 + Z.of_nat p) ^ Z.of_nat (p ^ S k') - 1).
    { rewrite (geom_sum_spec ((1 + Z.of_nat p) ^ Z.of_nat (p ^ k')) p).
      f_equal.
      rewrite <- Z.pow_mul_r; [| apply Nat2Z.is_nonneg | apply Nat2Z.is_nonneg].
      rewrite <- Nat2Z.inj_mul, Nat.mul_comm, <- Nat.pow_succ_r'.
      reflexivity. }
    rewrite <- Hfact in Hdvd.
    (* Hlow: p^(k'+1) | (1+p)^(p^k') - 1 *)
    pose proof (one_plus_p_pow_pk_dvd p k' Hprime) as Hlow.
    (* Hgeom_p: p | geom_sum A p *)
    assert (Hgeom_p : (Z.of_nat p |
                       geom_sum ((1 + Z.of_nat p) ^ Z.of_nat (p ^ k')) p)).
    { apply geom_sum_dvd_p.
      apply Z.divide_trans with (m := Z.of_nat (p ^ (k' + 1))).
      - rewrite Nat.add_1_r, Nat.pow_succ_r', Nat2Z.inj_mul.
        apply Z.divide_mul_l, Z.divide_refl.
      - exact Hlow. }
    (* Hgeom_nsq: p^2 ∤ geom_sum A p *)
    pose proof (geom_sum_not_dvd_p_sq p k' Hprime Hp2 Hodd) as Hgeom_nsq.
    (* Extract witnesses: A-1 = m * p^(k'+1), geom_sum A p = r * p *)
    destruct Hlow as [m Hm].
    destruct Hgeom_p as [r Hr].
    (* Hdvd now: p^(S k'+2) | (m*p^(k'+1))*(r*p) = p^(k'+2) * m*r *)
    assert (Heq : ((1 + Z.of_nat p) ^ Z.of_nat (p ^ k') - 1) *
                  geom_sum ((1 + Z.of_nat p) ^ Z.of_nat (p ^ k')) p =
                  Z.of_nat (p ^ (k' + 2)) * (m * r)).
    { rewrite Hm, Hr.
      assert (Hpow : Z.of_nat (p ^ (k' + 2)) = Z.of_nat p * Z.of_nat (p ^ (k' + 1))).
      { replace (k' + 2)%nat with (S (k' + 1))%nat by lia.
        rewrite Nat.pow_succ_r', Nat2Z.inj_mul. ring. }
      rewrite Hpow. ring. }
    assert (Hdvd' : (Z.of_nat (p ^ (S k' + 2)) | Z.of_nat (p ^ (k' + 2)) * (m * r))).
    { rewrite <- Heq. exact Hdvd. }
    (* p^(S k' + 2) = p * p^(k'+2) so p | m*r *)
    assert (Hp_mr : (Z.of_nat p | m * r)).
    { replace (S k' + 2)%nat with (S (k' + 2))%nat in Hdvd' by lia.
      rewrite Nat.pow_succ_r', Nat2Z.inj_mul in Hdvd'.
      assert (Hpkne : Z.of_nat (p ^ (k' + 2)) <> 0) by
        (pose proof (Nat.pow_nonzero p (k'+2) ltac:(lia)); lia).
      rewrite (Z.mul_comm (Z.of_nat p) (Z.of_nat (p^(k'+2)))) in Hdvd'.
      exact (proj1 (Z.mul_divide_cancel_l (Z.of_nat p) (m*r) (Z.of_nat (p^(k'+2))) Hpkne) Hdvd'). }
    (* p | m*r, p prime → p | m or p | r *)
    apply prime_mult in Hp_mr.
    + destruct Hp_mr as [Hm' | Hr'].
      * (* p | m → p^(k'+2) | A-1 → contradicts IH *)
        apply IH.
        replace (k' + 2)%nat with (S (k' + 1))%nat by lia.
        rewrite Nat.pow_succ_r', Nat2Z.inj_mul.
        rewrite Hm.
        (* goal: (Z.of_nat p * Z.of_nat (p^(k'+1)) | m * Z.of_nat (p^(k'+1))) *)
        destruct Hm' as [d Hd].
        exists d. rewrite Hd. ring.
      * (* p | r → p^2 | geom_sum A p → contradicts geom_not_sq *)
        apply Hgeom_nsq.
        rewrite Hr.
        replace (Z.of_nat (p ^ 2)) with (Z.of_nat p * Z.of_nat p) by
          (rewrite <- Nat2Z.inj_mul; f_equal;
           rewrite Nat.pow_succ_r', Nat.pow_succ_r'; simpl Nat.pow; rewrite Nat.mul_1_r; reflexivity).
        (* goal: (Z.of_nat p * Z.of_nat p | r * Z.of_nat p) *)
        destruct Hr' as [c Hc]. exists c. rewrite Hc. ring.
    + exact Hprime.
Qed.

(** ===== Phase 1 続き: (1+p) の位数 p^(n-1) ===== *)

(** 乗法群 (Z/nZ)* における gpow_nat の値:
    proj1_sig (gpow_nat (znz_units_group n Hn) a k) = (proj1_sig a)^k mod n。
    証明: k に関する帰納法。 *)
Lemma znz_units_gpow_nat_val : forall (n : nat) (Hn : (1 < n)%nat)
    (a : carrier (znz_units_group n Hn)) (k : nat),
  proj1_sig (gpow_nat (znz_units_group n Hn) a k) =
    Z.pow (proj1_sig a) (Z.of_nat k) mod Z.of_nat n.
Proof.
  intros n Hn a k.
  induction k as [| k' IH].
  - (* k = 0: e の値は 1, 1 mod n = 1 (n >= 2) *)
    simpl. symmetry. apply Z.mod_small. lia.
  - (* k = S k': op の定義から乗算 mod n *)
    (* まず LHS を展開して (a * a^k' mod n) mod n の形にする *)
    assert (Hstep : proj1_sig (gpow_nat (znz_units_group n Hn) a (S k')) =
              (proj1_sig a * proj1_sig (gpow_nat (znz_units_group n Hn) a k')) mod Z.of_nat n).
    { simpl. reflexivity. }
    rewrite Hstep, IH.
    rewrite Zmult_mod_idemp_r.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
    reflexivity.
Qed.

(** gcd(1+p, p) = 1: 1+p と p は互いに素。
    証明: d | 1+p かつ d | p ならば d | (1+p)-p = 1。 *)
Lemma one_plus_p_coprime_p : forall (p : nat),
    Z.gcd (1 + Z.of_nat p) (Z.of_nat p) = 1.
Proof.
  intros p.
  apply (proj2 (Zgcd_1_rel_prime _ _)).
  unfold rel_prime.
  apply Zis_gcd_intro.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros d Hd1 Hd2.
    replace 1 with ((1 + Z.of_nat p) - Z.of_nat p) by ring.
    exact (Z.divide_sub_r _ _ _ Hd1 Hd2).
Qed.

(** gcd(1+p, p^n) = 1: 1+p と p^n は互いに素 (n >= 1)。
    証明: n に関する帰納法。gcd(1+p, p) = 1 と rel_prime_mult を使う。 *)
Lemma one_plus_p_coprime_pn : forall (p n : nat),
    (1 <= n)%nat ->
    Z.gcd (1 + Z.of_nat p) (Z.of_nat (p^n)) = 1.
Proof.
  intros p n Hn.
  induction n as [| n' IH].
  - lia.
  - rewrite Nat.pow_succ_r', Nat2Z.inj_mul.
    apply (proj2 (Zgcd_1_rel_prime _ _)).
    apply rel_prime_mult.
    + apply (proj1 (Zgcd_1_rel_prime _ _)).
      exact (one_plus_p_coprime_p p).
    + destruct (Nat.eq_dec n' 0) as [H0 | Hn'].
      * subst. simpl.
        apply (proj1 (Zgcd_1_rel_prime _ _)).
        apply Z.gcd_1_r.
      * apply (proj1 (Zgcd_1_rel_prime _ _)).
        apply IH. lia.
Qed.

(** 素数 p^m の約数は p の冪:
    prime p, 0 < d, d | p^m ならば ∃ k <= m, d = p^k。
    証明: m に関する帰納法。
      - m = 0: d | 1 → d = 1 = p^0。
      - m = S m': gcd(d,p) = 1 か p | d かで場合分け。
          gcd = 1 の場合: ガウスの補題で d | p^m'。帰納法。
          p | d の場合: d = p*d', d' | p^m'。帰納法で d' = p^j → d = p^(j+1)。 *)
Lemma nat_prime_pow_divisors : forall (p m : nat),
    prime (Z.of_nat p) ->
    (2 <= p)%nat ->
    forall (d : nat),
    (0 < d)%nat ->
    Nat.divide d (p^m) ->
    exists k, (k <= m)%nat /\ (d = p^k)%nat.
Proof.
  intros p m Hprime Hp2.
  induction m as [| m' IH].
  - (* m = 0: d | 1 → d = 1 = p^0 *)
    intros d Hd Hdvd.
    simpl in Hdvd.
    exists 0%nat. split; [lia |].
    simpl. apply Nat.divide_1_r. exact Hdvd.
  - (* m = S m': d | p * p^m' *)
    intros d Hd Hdvd.
    rewrite Nat.pow_succ_r' in Hdvd.
    destruct (Nat.eq_dec (Nat.gcd d p) 1) as [Hgcd1 | Hgcd_ne1].
    + (* gcd(d,p) = 1: ガウスの補題で d | p^m' *)
      assert (Hdvd' : Nat.divide d (p^m')).
      { exact (Nat.gauss d p (p^m') Hdvd Hgcd1). }
      destruct (IH d Hd Hdvd') as [k [Hk Heq]].
      exists k. split; [lia | exact Heq].
    + (* gcd(d,p) ≠ 1: p | d *)
      (* gcd(d,p) | p なので gcd = p *)
      set (g := Nat.gcd d p).
      assert (Hg_dvd_p : Nat.divide g p) by apply Nat.gcd_divide_r.
      assert (Hgne : (0 < g)%nat).
      { unfold g.
        destruct (Nat.eq_dec (Nat.gcd d p) 0) as [H0 | Hne0].
        - exfalso. pose proof (Nat.gcd_eq_0 d p) as [Hfw _].
          destruct (Hfw H0) as [_ Hp0]. lia.
        - lia. }
      assert (Hg_eq_p : g = p).
      { (* Z.of_nat g | Z.of_nat p, g > 0, g ≠ 1 → g = p *)
        assert (HZg_dvd : (Z.of_nat g | Z.of_nat p)).
        { destruct Hg_dvd_p as [k Hk].
          exists (Z.of_nat k). rewrite Hk, Nat2Z.inj_mul. ring. }
        destruct (prime_divisors (Z.of_nat p) Hprime (Z.of_nat g) HZg_dvd)
          as [H | [H | [H | H]]].
        - (* Z.of_nat g = -1: 矛盾 (g > 0) *) lia.
        - (* Z.of_nat g = 1: 矛盾 (g ≠ 1 から) *)
          exfalso. apply Hgcd_ne1.
          unfold g in H. apply Nat2Z.inj. lia.
        - (* Z.of_nat g = Z.of_nat p: g = p *) apply Nat2Z.inj. lia.
        - (* Z.of_nat g = -Z.of_nat p: 矛盾 (g > 0) *) lia. }
      (* p | d *)
      assert (Hp_dvd_d : Nat.divide p d).
      { rewrite <- Hg_eq_p. apply Nat.gcd_divide_l. }
      destruct Hp_dvd_d as [d' Hd'].
      assert (Hd'pos : (0 < d')%nat) by (destruct d'; [rewrite Nat.mul_0_l in Hd'; lia | lia]).
      assert (Hd'_dvd : Nat.divide d' (p^m')).
      { apply (proj1 (Nat.mul_divide_cancel_l d' (p^m') p ltac:(lia))).
        rewrite (Nat.mul_comm p d'), <- Hd'. exact Hdvd. }
      destruct (IH d' Hd'pos Hd'_dvd) as [j [Hj Heq]].
      exists (S j). split.
      * lia.
      * rewrite Hd', Heq, Nat.pow_succ_r'. apply Nat.mul_comm.
Qed.


(** (Z/p^nZ)* における (1+p) mod p^n の乗法位数は p^(n-1) である。
    証明の方針:
      上界: one_plus_p_pow_pk_dvd より p^n | (1+p)^(p^(n-1)) - 1 なので
            gpow_nat elem (p^(n-1)) = e。よって d | p^(n-1)。
      分解: nat_prime_pow_divisors より d = p^k (k ≤ n-1)。
      下界 (n≥2): one_plus_p_pow_pk_not_dvd より (1+p)^(p^(n-2)) ≢ 1 (mod p^n)、
                  よって gpow_nat elem (p^(n-2)) ≠ e なので ¬(d | p^(n-2))。
      k ≤ n-2 なら p^k | p^(n-2) → 矛盾。よって k = n-1 で d = p^(n-1)。 *)
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
Proof.
  intros p n Hp2 Hprime Hodd Hn Hpn Hm elem Helem.
  (* d = mult_order を設定し仕様を取得 *)
  set (d := mult_order (znz_units_group (p^n) Hpn) (p^(n-1)*(p-1)) Hm elem).
  pose proof (mult_order_spec (znz_units_group (p^n) Hpn) (p^(n-1)*(p-1)) Hm elem)
    as [Hd_pos _].
  (* 上界: gpow_nat elem (p^(n-1)) = e *)
  assert (Hpow_up : gpow_nat (znz_units_group (p^n) Hpn) elem (p^(n-1))%nat =
                    e (znz_units_group (p^n) Hpn)).
  { apply sig_eq.
    rewrite znz_units_gpow_nat_val, Helem, Z.mod_pow_l.
    simpl proj1_sig.
    pose proof (one_plus_p_pow_pk_dvd p (n-1)%nat Hprime) as Hdvd.
    replace (n-1+1)%nat with n in Hdvd by lia.
    apply dvd_to_one_mod; [lia | exact Hdvd]. }
  (* d | p^(n-1) *)
  assert (Hdvd_upper : Nat.divide d (p^(n-1))%nat).
  { exact (proj1 (mult_order_divides (znz_units_group (p^n) Hpn) (p^(n-1)*(p-1))
                   Hm elem (p^(n-1))%nat) Hpow_up). }
  (* nat_prime_pow_divisors: d = p^k, k ≤ n-1 *)
  destruct (nat_prime_pow_divisors p (n-1)%nat Hprime Hp2 d Hd_pos Hdvd_upper)
    as [k [Hk Hdeq]].
  (* k = n-1 を示す *)
  assert (Hk_eq : (k = n-1)%nat).
  { assert (Hcases : (n-1 <= k)%nat \/ (k < n-1)%nat) by lia.
    destruct Hcases as [Hle | Hlt]; [lia |].
    (* k < n-1 → 矛盾 *)
    exfalso.
    assert (Hn2 : (2 <= n)%nat) by lia.
    (* d = p^k | p^(n-2) since k ≤ n-2 *)
    assert (Hdvd_lo : Nat.divide d (p^(n-2))%nat).
    { rewrite Hdeq. exists (p^(n-2-k))%nat.
      rewrite <- Nat.pow_add_r. f_equal. lia. }
    (* gpow_nat elem (p^(n-2)) = e *)
    assert (Hpow_lo : gpow_nat (znz_units_group (p^n) Hpn) elem (p^(n-2))%nat =
                      e (znz_units_group (p^n) Hpn)).
    { exact (proj2 (mult_order_divides (znz_units_group (p^n) Hpn) (p^(n-1)*(p-1))
                     Hm elem (p^(n-2))%nat) Hdvd_lo). }
    (* (1+p)^(p^(n-2)) mod p^n = 1 *)
    assert (Hval : (1 + Z.of_nat p)^Z.of_nat (p^(n-2)) mod Z.of_nat (p^n) = 1).
    { assert (Hv1 : proj1_sig (gpow_nat (znz_units_group (p^n) Hpn) elem (p^(n-2))%nat) = 1).
      { rewrite Hpow_lo. reflexivity. }
      rewrite znz_units_gpow_nat_val, Helem, Z.mod_pow_l in Hv1.
      exact Hv1. }
    (* p^n | (1+p)^(p^(n-2)) - 1 を構成し one_plus_p_pow_pk_not_dvd に矛盾 *)
    apply (one_plus_p_pow_pk_not_dvd p (n-2)%nat Hprime Hp2 Hodd).
    replace (n-2+2)%nat with n by lia.
    exists ((1+Z.of_nat p)^Z.of_nat (p^(n-2)) / Z.of_nat (p^n)).
    pose proof (Z.div_mod ((1+Z.of_nat p)^Z.of_nat (p^(n-2)))
                           (Z.of_nat (p^n)) ltac:(lia)) as Hdm.
    lia. }
  (* d = p^(n-1) *)
  rewrite Hdeq. f_equal. exact Hk_eq.
Qed.
