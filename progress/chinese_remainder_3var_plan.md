# Proof Plan: chinese_remainder_3（継続版）

## Goal
`pairwise_coprime3 p q r` のもとで、
`n mod p = a`, `n mod q = b`, `n mod r = c` を同時に満たす
`n` が `[0, p*q*r)` に唯一存在することを、
実装・検証・記録まで含めて完了状態にする。

## 現在の到達点（2026-04-04確認）
- `integer.v` には以下が実装済み:
	- `pairwise_coprime3_*`
	- `pairwise_coprime3_gcd_pq_r`
	- `cong_of_cong_mul_l`, `cong_of_cong_mul_r`
	- `coprime_divide_mul_3`
	- `crt_exists_3`, `crt_unique_3`
	- `chinese_remainder_3`
- 未証明としての `Admitted` は本系列には残っていない。
- 最終確認の主タスクは「コンパイル検証ログの確定」と「進捗文書の同期」。

## Continuation Strategy
1. 実装済み証明を壊さず、検証と記録の整合性を優先する。
2. 3変数CRTを今後の再利用単位として切り出せるよう、依存補題を明示する。
3. 次の拡張（4変数以上/一般n変数）に進める準備を、この段階で計画化する。

## Continuation Tasks
- [ ] `verify_crt3_compile`: `rocq compile integer.v` を実行し、成功を `progress` に反映
- [ ] `sync_crt3_progress`: `progress/chinese_remainder_3var_progress.md` の TODO を解消し、状態を確定
- [ ] `document_crt3_dependencies`: 3変数CRTが依存する補題列を短く整理して追記
- [ ] `plan_crt_n_extension`: n変数化に向けた次プラン（帰納法または逐次合成）の下書きを作成

## Suggested Proof Order (Continuation)
1. `verify_crt3_compile`
2. `sync_crt3_progress`
3. `document_crt3_dependencies`
4. `plan_crt_n_extension`

## Exit Criteria
- `integer.v` のコンパイル成功を確認済み。
- `progress/chinese_remainder_3var_progress.md` が TODO なし。
- 3変数CRTの依存関係が短く整理され、次拡張の入口が明確。
