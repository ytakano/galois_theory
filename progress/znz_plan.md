# Proof Plan: Z/nZ (Residue Class Group)

## Goal

Z/nZ を群として `integer.v` に定義し、それが巡回群でもあることを示す。

## 定義の構成

1. **`znz_group n Hn : Group`**
   - 台集合: `{x : Z | 0 <= x < Z.of_nat n}`
   - 演算: `(a + b) mod n`
   - 単位元: `0`
   - 逆元: `(-a) mod n`

2. **`znz_gpow_nat_val`** (補助補題)
   - `proj1_sig (gpow_nat (znz_group n Hn) gen k) = Z.of_nat k mod Z.of_nat n`
   - k に関する帰納法で証明

3. **`znz_cyclic_group n Hn : CyclicGroup`**
   - 生成元: `[1 mod n]`（n=1 のとき [0]、n≥2 のとき [1]）
   - 巡回性: 任意の元 [x] に対して k=x を選ぶ

## 証明で使うキーレンマ

| 補題 | 用途 |
|------|------|
| `Z.mod_pos_bound` | sigma 型の範囲証明 |
| `Zplus_mod_idemp_l` | 結合律・逆元 |
| `Zplus_mod_idemp_r` | 結合律・逆元 |
| `Z.mod_small` | 単位元公理 |
| `Zmod_0_l` | 逆元公理の最終ステップ |
| `Z.add_opp_diag_l/r` | 逆元公理 |
| `gpow_of_nat` | 巡回性証明 |
| `Z2Nat.id` | 巡回性証明 |
| `Nat2Z.inj_succ` | 補助補題の帰納ステップ |

## サブレンマの証明順序

- [x] `znz_group` — 群公理の全証明
- [x] `znz_gpow_nat_val` — 生成元の冪の値
- [x] `znz_cyclic_group` — 巡回群としての構造

## 完了

2026-04-03: znz_group, znz_gpow_nat_val, znz_cyclic_group を実装。
