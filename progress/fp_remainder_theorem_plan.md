# Proof Plan: fp_remainder_theorem (Fp上の剰余の定理)

## Goal

体 F（特に有限体 Fp = Z/pZ）上の多項式 f(x) を (x - a) で割ると、余りは f(a) となることを証明する。

主定理 (抽象 Field レベル):
```coq
Theorem poly_remainder_theorem :
  forall (F : Field) (f : list (ring_carrier F)) (a x : ring_carrier F),
    poly_eval F f x =
    ring_add F
      (ring_mul F (ring_add F x (ring_neg F a))
                  (poly_eval F (poly_synthetic_div F f a) x))
      (poly_eval F f a).
```

系 (Fp への特化):
```coq
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
```

## Proof Strategy

多項式を係数リスト `list (ring_carrier F)` で表現する（小端表現: インデックス i が x^i の係数）。

```
[c0, c1, ..., cn]  =  c0 + c1*x + c2*x^2 + ... + cn*x^n
```

- `poly_eval` をホーナー法で定義:
  `eval [] x = 0`
  `eval (c :: cs) x = c + x * eval cs x`

- `poly_synthetic_div` を再帰で定義（合成除算）:
  `div [] a = []`
  `div [c] a = []`
  `div (c :: cs) a = poly_eval cs a :: div cs a`

数学的根拠: f = c :: cs のとき、csの帰納法仮定 eval cs x = (x-a)*q(x) + eval cs a を用いると、
  eval (c :: cs) x
  = c + x * eval cs x
  = c + x * ((x-a)*q(x) + eval cs a)
  = c + (x-a)*x*q(x) + x * eval cs a
  = (x-a)*(x*q(x) + eval cs a) + c + a * eval cs a   ← 分配法則
  = (x-a) * (eval cs a :: q)(x) + eval (c :: cs) a

ここで `(eval cs a :: q)` が div (c :: cs) a に対応する。
乗法可換律 `field_mul_comm` を利用（Field 上で証明するため OK）。

## Necessary Definitions

### 1. `poly_eval`

```coq
(** ホーナー法による多項式評価 *)
Fixpoint poly_eval (F : Field) (f : list (ring_carrier F)) (x : ring_carrier F)
  : ring_carrier F :=
  match f with
  | [] => ring_zero F
  | c :: cs => ring_add F c (ring_mul F x (poly_eval F cs x))
  end.
```

### 2. `poly_synthetic_div`

```coq
(** 合成除算：(x - a) で割ったときの商多項式 *)
Fixpoint poly_synthetic_div (F : Field) (f : list (ring_carrier F)) (a : ring_carrier F)
  : list (ring_carrier F) :=
  match f with
  | [] | [_] => []
  | _ :: cs => poly_eval F cs a :: poly_synthetic_div F cs a
  end.
```

## Proposed Lemmas

- [ ] `poly_eval_nil`: `poly_eval F [] x = ring_zero F` （定義から直ちに）
- [ ] `poly_eval_cons`: `poly_eval F (c :: cs) x = ring_add F c (ring_mul F x (poly_eval F cs x))`（定義から直ちに）
- [ ] `poly_synthetic_div_nil`: `poly_synthetic_div F [] a = []`（定義から直ちに）
- [ ] `poly_synthetic_div_singleton`: `poly_synthetic_div F [c] a = []`（定義から直ちに）
- [ ] `poly_synthetic_div_cons`: `poly_synthetic_div F (c :: cs) a = poly_eval F cs a :: poly_synthetic_div F cs a`
  （cs が空でない場合。但し `cs = []` のとき div [c] a = [] だが `poly_eval F [] a :: div [] a = [0]` となり不一致。→ ケース分割で対処）
- [ ] `poly_remainder_step`: 帰納ステップの代数補題（主定理の `c :: cs` 部分）
- [ ] `poly_remainder_theorem`: リスト帰納法で証明
- [ ] `fp_remainder_theorem`: `poly_remainder_theorem` を `znz_p_field p Hp` に適用

**注意**: `poly_synthetic_div` は match の `[]` と `[_]` で同じく `[]` を返すが、
`[_]` のケースは内部的に `_ :: []` として扱われる。Rocq のパターンマッチで:
```
match f with
| [] => []
| [_] => []
| _ :: cs => poly_eval F cs a :: poly_synthetic_div F cs a
end
```
は `c :: []` と `c :: (_ :: _)` で正しくケース分割できる。

## Proof Order

1. `poly_eval_nil` (自明)
2. `poly_eval_cons` (自明)
3. `poly_synthetic_div_nil` (自明)
4. `poly_synthetic_div_singleton` (自明)
5. `poly_synthetic_div_cons` (cs ≠ [] のとき定義から、cs = [] のとき singleton で代替)
6. `poly_remainder_theorem` (リスト帰納法 + 代数計算)
7. `fp_remainder_theorem` (適用のみ)
