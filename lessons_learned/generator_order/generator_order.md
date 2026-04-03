はい、できます。`generator_order` はかなり自然に小さな Lemma に分割できます。
特に、いまの証明方針の核は

1. 有限個しか元がないので、`g^0, g^1, ..., g^m` の中に重複がある
2. 重複から `g^d = e` となる正の周期 `d` が得られる
3. 生成元なので、群全体は `g^0, ..., g^(d-1)` で尽くされる
4. 群の位数が `m` だから、`d <= m` かつ `m <= d` より `d = m`
5. よって `g^m = e`

という流れです。
この流れに沿って Lemma を切るのがよいです。元ファイルの `gpow_add`, `gpow_mul` などはすでにかなり強いので、土台はあります。

---

## まず気をつけたい点

コメント中にある

> `g^0, g^1, ..., g^(m-1)` はすべて異なる (単射性より)

は、そのままではまだ言えません。
`GroupOrder C m` の単射性は **`carrier C -> Fin.t m` の単射**であって、`n ↦ g^n` の単射ではないからです。
なので先に

* `f : carrier C -> Fin.t m` を取り出す
* `f (g^0), f (g^1), ..., f (g^m)` を考える
* `Fin.t m` に `m+1` 個入れているので重複が出る

という **鳩ノ巣原理** の形に持っていく必要があります。

---

## おすすめの分割

### 1. 位数の証明から bijection を取り出す補題

`GroupOrder` はすでに

* `f : carrier G -> Fin.t n`
* injective
* surjective

の形なので、これはそのまま使えます。
ただし後で何度も使うなら、取り出しやすい補題にしておくと楽です。

```coq
Lemma group_order_bijection :
  forall (G : Group) (n : nat),
    GroupOrder G n ->
    exists f : carrier G -> Fin.t n,
      (forall x y, f x = f y -> x = y) /\
      (forall i : Fin.t n, exists x, f x = i).
```

これは単なる unpack 用です。

---

### 2. 「有限集合 `Fin.t m` に `m+1` 個入れると重複する」補題

これが有限性側の中心です。

欲しい形はたとえば

```coq
Lemma pigeonhole_Fin :
  forall (m : nat) (h : nat -> Fin.t m),
    exists i j : nat,
      i < j /\ j <= m /\ h i = h j.
```

ただしこの形は `h` が全 `nat` 上で定義されているので、実装はやや面倒です。
Rocq/Coq 的には、長さ `m+1` の列を扱う形のほうがやりやすいこともあります。

たとえば

```coq
Lemma pigeonhole_powers :
  forall (m : nat) (f : carrier C -> Fin.t m),
    (forall x y, f x = f y -> x = y) ->
    exists i j : nat,
      i < j /\ j <= m /\
      f (gpow C (generator C) (Z.of_nat i))
      = f (gpow C (generator C) (Z.of_nat j)).
```

のように、`g^k` に特化した補題にしてしまってもよいです。

ここは標準ライブラリだけでやると少し重いので、最初は `Admitted` で先へ進み、最後に詰めるのもありです。

---

### 3. 重複した冪から周期を得る補題

`g^i = g^j` かつ `i < j` から `g^(j-i) = e` を出す補題です。
これは群の計算側の核心ですが、すでにある `gpow_add` を使えば比較的きれいに出ます。

```coq
Lemma equal_powers_imply_period :
  forall (G : Group) (a : carrier G) (i j : nat),
    i < j ->
    gpow G a (Z.of_nat i) = gpow G a (Z.of_nat j) ->
    gpow G a (Z.of_nat (j - i)) = e G.
```

証明イメージは

* `j = i + (j-i)`
* `g^j = g^(i + (j-i)) = g^i * g^(j-i)`
* 仮定 `g^i = g^j` を代入すると
  `g^i = g^i * g^(j-i)`
* 左から `inv (g^i)` を掛けて `g^(j-i) = e`

です。

この「左から逆元を掛けて消す」操作は補題化しておくと便利です。

```coq
Lemma op_cancel_l :
  forall (G : Group) (x y z : carrier G),
    op G x y = op G x z -> y = z.
```

これを先に作ると証明がかなり楽になります。

---

### 4. 周期 `d` があると、全要素は最初の `d` 個の冪で表せる補題

`g^d = e` なら、指数を `d` で割った余りに落とせます。

```coq
Lemma gpow_mod_period :
  forall (G : Group) (a : carrier G) (d n : nat),
    gpow G a (Z.of_nat d) = e G ->
    gpow G a (Z.of_nat n)
    = gpow G a (Z.of_nat (n mod d)).
```

これは `n = q*d + r` を使って

* `g^n = g^(q*d + r) = g^(q*d) * g^r`
* `g^(q*d) = (g^d)^q = e^q = e`

で出せます。
既存の `gpow_add`, `gpow_mul`, `gpow_nat_e` が使えます。

---

### 5. 生成元なら、周期 `d` があると群の元は高々 `d` 個しかない補題

これが「`m <= d`」を出すための補題です。

```coq
Lemma cyclic_group_order_le_period :
  forall (C : CyclicGroup) (m d : nat),
    GroupOrder C m ->
    0 < d ->
    gpow C (generator C) (Z.of_nat d) = e C ->
    m <= d.
```

証明の考え方は：

* 任意の `x : carrier C` について、巡回性より `x = g^z`
* その `z` を `d` 未満の代表に落とせることを示す
* したがって群全体は高々 `d` 個の元で尽くされる

ただしここで `z : Z` を `0 <= r < d` に落とすには、少し整数の補題が要ります。
なので最初は自然数冪だけに限定したいなら、先に

```coq
forall x, exists k : nat, k < d /\ x = gpow C (generator C) (Z.of_nat k)
```

を示す補題に切ってもよいです。

---

### 6. `d <= m` は自明

さっきの鳩ノ巣から得られる `i < j <= m` に対して `d := j - i` とすれば

```coq
0 < d /\ d <= m
```

はすぐ出ます。

---

## 最終的な `generator_order` の組み立て

こういう感じの骨格になります。

```coq
Lemma generator_order : forall (C : CyclicGroup) (m : nat),
  GroupOrder C m ->
  gpow C (generator C) (Z.of_nat m) = e C.
Proof.
  intros C m Hord.
  destruct (group_order_bijection C m Hord) as [f [Hinj Hsurj]].

  (* 鳩ノ巣で 0..m の冪に重複 *)
  destruct (pigeonhole_powers C m f Hinj) as [i [j [Hij_lt [Hj_le Heqf]]]].
  assert (Heqpow :
    gpow C (generator C) (Z.of_nat i) =
    gpow C (generator C) (Z.of_nat j)).
  { apply Hinj. exact Heqf. }

  set (d := j - i).
  assert (Hd_pos : 0 < d) by lia.
  assert (Hd_le_m : d <= m) by lia.
  assert (Hd_period :
    gpow C (generator C) (Z.of_nat d) = e C).
  { apply equal_powers_imply_period with (i := i) (j := j); auto. }

  (* 周期 d から位数 m <= d *)
  assert (Hm_le_d : m <= d).
  { apply cyclic_group_order_le_period with (d := d); auto. }

  assert (Hd_eq_m : d = m) by lia.
  subst d.
  exact Hd_period.
Qed.
```

---

## さらに小さくすると楽な補題

証明中で頻出しそうなのは次です。

### 消去則

```coq
Lemma op_cancel_l :
  forall (G : Group) (x y z : carrier G),
    op G x y = op G x z -> y = z.

Lemma op_cancel_r :
  forall (G : Group) (x y z : carrier G),
    op G y x = op G z x -> y = z.
```

### 冪の 0 と差

```coq
Lemma gpow_0 :
  forall (G : Group) (a : carrier G),
    gpow G a 0 = e G.

Lemma gpow_sub_nat :
  forall (G : Group) (a : carrier G) (i j : nat),
    i <= j ->
    gpow G a (Z.of_nat j)
    = op G (gpow G a (Z.of_nat i))
           (gpow G a (Z.of_nat (j - i))).
```

これは `j = i + (j-i)` を `gpow_add` に入れるだけです。

### 周期の倍数は単位元

```coq
Lemma gpow_period_multiple :
  forall (G : Group) (a : carrier G) (d q : nat),
    gpow G a (Z.of_nat d) = e G ->
    gpow G a (Z.of_nat (q * d)) = e G.
```

これは `gpow_mul` が使えます。

---

## 実際にはどこが難所か

難所は主に2つです。

### 1. 鳩ノ巣原理

`Fin.t m` に `m+1` 個入れると重複、という補題です。
数学的には簡単ですが、Rocq で素朴にやると少し手間です。

### 2. 「周期 d なら元は高々 d 個」

`cyclic_property` が `exists n : Z` の形なので、整数指数を余りに落とす補題が要ります。
ここは `Z.modulo` と `gpow_add`, `gpow_mul` をつなぐ部分がやや重いです。

---

## 実用的な進め方

おすすめは次の順です。

1. まず群の計算だけで済む補題を全部証明

   * `op_cancel_l`
   * `equal_powers_imply_period`
   * `gpow_mod_period`
2. 次に有限性の補題を別途用意

   * `pigeonhole_Fin`
3. 最後に `cyclic_group_order_le_period` を証明
4. `generator_order` を組み立てる

---

## 別案

もっと直接的にやるなら、

* `x ↦ f (g^x)` を `0..m` で見る
* 最小の重複差 `d` を取る
* 最小性から `g^0, ..., g^(d-1)` は相異なる
* しかも全体を生成するのでちょうど `d` 個
* よって `d = m`

という「最小周期」を使う方法もあります。
ただし Rocq では「最小のものを取る」議論の方がむしろ重くなりやすいです。
なので最初は **`m <= d` と `d <= m` を別々に出す方針** のほうが機械化しやすいです。

---

必要なら次に、上で挙げた補題のうち
`op_cancel_l` と `equal_powers_imply_period` から具体的な Rocq コードを書きます。
