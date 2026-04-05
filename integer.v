Require Import Corelib.Init.Peano Corelib.Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import ZArith ZArith.Znumtheory Init.Logic.
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

(** 素数 p のとき Z/pZ は体である。
    証明方針:
      - 台集合: carrier = Z (mod p 演算で正規化)
      - 加法: (Z, +, 0, neg) mod p で加法群
      - 乗法: mul = fun a b => a*b mod p、単位元 = 1 mod p
      - 逆元: p が素数なら a ≢ 0 (mod p) → gcd(a,p)=1 → Bezout 係数が逆元
      - 1 ≠ 0: p ≥ 2 なので 1 mod p = 1 ≠ 0

    TODO: refine による実装は field_inv の型 (Z → Z vs sigma 型) の整合を
    znz_units_inv_val と合わせる必要がある。現在は Admitted。  *)
Definition znz_p_field (p : nat) (Hp : prime (Z.of_nat p)) : Field.
Admitted.
