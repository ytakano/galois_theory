# Proof Plan: fp_poly_roots_bound (Fp上のn次方程式の解はn個以下)

## Goal

```coq
(* 主定理: 体上のn次多項式はたかだかn個の根を持つ *)
Theorem poly_roots_bound :
  forall (F : Field) (f : list (ring_carrier F)),
    poly_nonzero_leading F f ->
    forall (roots : list (ring_carrier F)),
      NoDup roots ->
      (forall a, In a roots -> poly_eval F f a = ring_zero F) ->
      (length roots < length f)%nat.

(* 系: Fp上の多項式版 *)
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
```

## Proof Strategy

`length f` に関する帰納法。

- **Base** (`length f = 1`): 非零定数 `[c]` の場合。`poly_eval F [c] x = c ≠ 0` なので根がない。→ `length roots = 0 < 1`。
- **Step** (`length f = n+1`, `n ≥ 1`): `poly_nonzero_leading` かつ先頭係数非零と仮定。
  - `roots = []` なら自明 (`0 < n+1`)。
  - `roots = a :: rest` なら:
    1. `poly_factor_of_root`: `f(a) = 0` ⟹ `f(x) = (x-a)*q(x)` (q = `poly_synthetic_div F f a`)
    2. `poly_synthetic_div_length`: `length q = length f - 1 = n`
    3. `poly_nonzero_leading_div`: q の先頭係数 = f の先頭係数 ≠ 0
    4. `NoDup (a::rest)` ⟹ `∀ b ∈ rest, b ≠ a`
    5. `poly_div_root`: `f(b) = 0`, `b ≠ a` ⟹ `q(b) = 0` (field_no_zero_divisors 使用)
    6. IH: `length rest < length q = n`
    7. `length (a :: rest) = 1 + length rest ≤ n < n + 1 = length f` ✓

## Proposed Lemmas

- [x] `ring_sub_zero_iff_eq`: `ring_add R a (ring_neg R b) = ring_zero R ↔ a = b`
- [x] `poly_synthetic_div_length`: `length (poly_synthetic_div F (c :: cs) a) = length cs`
- [x] `poly_eval_single`: `poly_eval F [c] x = c`
- [x] `last_cons_nonempty`: `t ≠ [] → last (h :: t) d = last t d`
- [x] `poly_synthetic_div_last`: 合成除算は先頭係数(last 要素)を保存する
- [x] `poly_nonzero_leading` (定義)
- [x] `poly_nonzero_leading_div`: 長さ≥2 の先頭係数非零多項式の合成除算も先頭係数非零
- [x] `poly_const_nonzero_no_root`: 非零定数多項式は根なし
- [x] `poly_div_root`: `f(a)=0`, `f(b)=0`, `b≠a` ⟹ `(poly_synthetic_div F f a)(b) = 0`
- [x] `poly_roots_bound` (主定理) ✓
- [x] `fp_poly_roots_bound` (系) ✓

## Proof Order

1. `ring_sub_zero_iff_eq`
2. `poly_synthetic_div_length`
3. `poly_eval_single`
4. `poly_synthetic_div_last`
5. `poly_nonzero_leading` (定義)
6. `poly_nonzero_leading_div`
7. `poly_const_nonzero_no_root`
8. `poly_div_root`
9. `poly_roots_bound` (主定理)
10. `fp_poly_roots_bound` (系)
