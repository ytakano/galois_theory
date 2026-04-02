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
    (0, n): 単位元の左中立性から自明。
    (+, +): Pos2Nat.inj_add と gpow_nat_add を使用。
    (-, -): 逆元側の gpow_nat_add を使用。
    (+, -), (-, +): 正負の打ち消しが生じる場合は符号の大小で再度分岐し,
                    inv_right / inv_left と id_right / id_left を使用。  *)
Lemma gpow_add : forall (G : Group) (a : carrier G) (m n : Z),
  gpow G a (m + n) = op G (gpow G a m) (gpow G a n).
Proof.
Admitted.

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

(** 単位元の冪: e^n = e  *)
Lemma gpow_nat_e : forall (G : Group) (n : nat),
  gpow_nat G (e G) n = e G.
Proof.
  intros G n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. apply id_left.
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
Admitted.

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

(** 巡回群の部分群定理:
    位数 m > 0 の巡回群 C の任意の部分群 H に対して,
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
  (0 < m)%nat ->
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
Admitted.