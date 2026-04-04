# Proof Plan: znz_units_group (既約剰余類群)

## Goal

```coq
Definition znz_units_group (n : nat) (Hn : (1 < n)%nat) : Group.
```

Z/nZ のうち n と互いに素な元のみからなる集合 `(Z/nZ)*` を乗算に関する群として定義する。

- 台集合: `{x : Z | 0 <= x < Z.of_nat n /\ Z.gcd x (Z.of_nat n) = 1}`
- 演算: `[a] * [b] := [(a * b) mod n]`
- 単位元: `[1]`
- 逆元: ベズーの補題から構成

## Proof Strategy

1. **閉包性（乗算）**: `Z.gcd a n = 1 /\ Z.gcd b n = 1 → Z.gcd (a*b mod n) n = 1`
   - `Z.gcd_mul_r` または `Z.Gauss` を活用
2. **単位元の存在**: `Z.gcd 1 n = 1` かつ `0 < 1 < n` (n > 1 のとき)
3. **逆元の存在**: `Z.gcd a n = 1 → ∃ b, a*b ≡ 1 (mod n) /\ Z.gcd b n = 1`
   - 既存の `nat_coprime_bezout` を利用
4. **群公理**: 結合律・左右単位元・左右逆元

## Proposed Lemmas

- [x] `znz_gcd_one`: `Z.gcd 1 (Z.of_nat n) = 1`（単位元の互素性）
- [x] `znz_gcd_mod_eq`: `Z.gcd (a mod Z.of_nat n) (Z.of_nat n) = Z.gcd a (Z.of_nat n)`（mod と gcd の交換）
- [x] `znz_gcd_mul_coprime`: `Z.gcd a (Z.of_nat n) = 1 → Z.gcd b (Z.of_nat n) = 1 → Z.gcd (a * b) (Z.of_nat n) = 1`（乗算の閉包性）
- [x] `znz_coprime_bezout_inv`: `Z.gcd a (Z.of_nat n) = 1 → 0 <= a < Z.of_nat n → ∃ b, 0 <= b < Z.of_nat n /\ a * b ≡ 1 (mod n) /\ Z.gcd b (Z.of_nat n) = 1`（逆元の存在）
- [x] `znz_units_group`: メイン定義

## Proof Order

1. `znz_gcd_one` ✓
2. `znz_gcd_mod_eq` ✓
3. `znz_gcd_mul_coprime` ✓
4. `znz_coprime_bezout_inv` ✓
5. `znz_units_group` ✓ (main goal)

## 完了

2026-04-04: 全補題・定義の証明が完了。`rocq compile integer.v` でエラーなし。

## 使用予定の標準ライブラリ補題

| 補題 | 用途 |
|------|------|
| `Z.gcd_1_l` / `Z.gcd_1_r` | gcd(1, n) = 1 |
| `Z.gcd_mod` | gcd(a mod n, n) = gcd(a, n) |
| `Z.Gauss` | gcd(a,n)=1 かつ n|a*b → n|b (乗算閉包に応用) |
| `Z.gcd_mul_r` / `Znumtheory.Zgcd_mult_rel_prime` | gcd(a*b, n)=1 when gcd(a,n)=gcd(b,n)=1 |
| `Z.mod_pos_bound` | sigma 型の範囲証明 |
| `Zmult_mod_idemp_l/r` | 結合律 |
| `Z.mod_small` | 単位元公理 |
| `nat_coprime_bezout` | 逆元存在 (既存) |
| `sig_eq` | sigma 型の等号 (既存) |
