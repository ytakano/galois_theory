# ガロア理論

Claude Codeの実験のためのCoq/Rocqプロジェクトです。現在は整数/数論の基礎を実装中で、今後ガロア理論の定式化を進め、生成AIの限界に挑戦していく予定です。

# ファイル

- [integer.v](./integer.v): 整数の定義と性質

現在、整数の定義と性質を扱うファイルは `integer.v` を実装中です。今後、ガロア理論に関連する他のファイルも追加される予定です。

# チェック方法

`rocq compile integer.v`

コンパイルエラーとなった場合、以下のコマンドでエラー箇所のゴールを確認できます。

`python3 rocq_error_goal.py integer.v`
