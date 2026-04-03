# Lessons learned

このプロジェクトを進める中で得られた洞察や学びをまとめます。

## `gpow_add`の証明でトークン制限に達した

整数指数の加法性を証明する`gpow_add`をClaude Codeに証明させようとしましたが、証明が複雑だったためか、トークン制限に達して証明が完了しませんでした。

補題`gpow_add`は、以下のようになります。

```coq
Lemma gpow_add : forall (G : Group) (a : carrier G) (m n : Z),
  gpow G a (m + n) = op G (gpow G a m) (gpow G a n).
```

数式で書くと、以下のようになります。

```math
g^{m + n} = g^m \cdot g^n
```

mとnは整数であり、gはある群Gの要素です。

なお、べき乗する値が0の場合は単位元になり、負の値の場合は逆元をべき乗することになります。

```math
g^0 = e \quad \text{(単位元)}
```

```math
g^{-1} = \text{gの逆元}
```

```math
g^{-n} = (g^{-1})^n \quad \text{(べきの値が負の場合)}
```

となります。

`gpow_add`の証明は、mとnの符号に応じて、場合わけで証明を進めることができます。実は、`gpow_add`の定義もClaude Codeに書いてもらったのですが、そのコメントに場合分けで証明するとよいと、Claude Code自身でコメントしていました。

そこで、mとnの符号に応じて場合分けし、`gpow_add_pos_pos`、`gpow_add_neg_neg`、`gpow_add_pos_neg`、`gpow_add_neg_pos`の4つの補題を順に証明していくと、無事に、`gpow_add`の証明が完了しました。

ただし、`gpow_add_pos_pos`は、著者が証明しました。これは、トークン制限でClaude Codeが利用できなかったためです。証明には、ChatGPTを利用し、対話的に証明を進めていきました。

## `generator_order`の証明でトークン制限に達した

`generator_order`の証明も、トークン制限に達して証明が完了しませんでした。`generator_order`は、巡回群の性質に関する定理で、生成元を位数でべき乗すると単位元になることを示すものです。Rocqで記述すると以下のようになります。

```coq
Lemma generator_order : forall (C : CyclicGroup) (m : nat),
  GroupOrder C m ->
  gpow C (generator C) (Z.of_nat m) = e C.
```

ここで、`GroupOrder C m`は、巡回群Cの位数がmであることを表す述語です。`gpow`は、群の要素を整数でべき乗する関数で、`generator C`は、巡回群Cの生成元を表します。`e C`は、巡回群Cの単位元を表します。

数式で書くと、以下が成り立つということです。ここで、`g`は巡回群Cの生成元、`m`はCの位数、`e`はCの単位元を表します。

```math
g^m = e
```

`gpow_add`の反省を活かし、`generator_order`の証明をいくつかの補題に分割して、段階的に証明を進めていきました。その際、まず、ChatGPTで、`generator_order`の証明の分割と方針を立ててもらいました。その結果は、[generator_order.md](lessons_learned/generator_order/generator_order.md)にあります。

Claude Codeで証明を進める際、一つずつ補題を証明していきました。補題を一つ証明する毎に、`/clear`コマンドで、証明の履歴を消去していきました。これにより、トークンを節約することができるそうです。また、証明をする際に、[generator_order_progress.md](lessons_learned/generator_order/generator_order_progress.md)のように、証明の進捗や方針を記録していきました。

証明中に、これらはスキル化できると思いついき、次節で述べるようなスキルを作成しました。

## 証明のためのスキル作成

`gpow_add`と`generator_order`の証明でトークン制限に達したことを受けて、証明のためのスキルを作成することにしました。証明するためには、まず、証明の方針を立て、証明に必要な補題を提案し、それらを順番に証明していくことが重要だと考えました。そこで、証明する際は、自動的にこれを行うよう、スキルを作成しました。スキルの詳細は、[ROCQ.md](.claude/skills/ROCQ.md)に記載しています。

まずはじめに、スキルの下書きを日本語で作成しました。[ROCQ_JP.md](lessons_learned/skills/ROCQ_JP.md)にあります。その後、Claudeに内容のブラッシュアップと英語化を行ってもらいました。

しかし、Claud CodeをPlanモードで利用すると、このスキルを呼び出すことができないことがわかりました。そこで、Planモードであっても、このスキルを呼び出すように、[CLAUDE.md](CLAUDE.md)のProof Workflowのセクションに、以下のように追記するよう指示しました。

```markdown
**IMPORTANT**: Always invoke the `/rocq-prover` skill **before writing any Rocq code**, even after Plan mode. Do not implement proofs directly without going through the skill.
```

Planモードでは、同じようなことを行うので、もしかしたら、このスキルは必要ない可能性もあります。

## 推論に不要なファイルやディレクトリの明示化

証明する際に必要ないファイルやディレクトリを明示的に記載することにしました。これにより、証明に集中できるようになり、トークンも節約できると考えました。推論に不要なファイルは、[settings.local.json](.claude/settings.local.json)の`deny`セクションに記載しています。

## 推論の深さを推定

推論の深さをClaude Codeに推定させることにしました。これにより、推論の深さに応じて、適切な推論方法を選択できるようになると考えました。推論の深さは、単純なタスク（例：事実の検索、単一ファイルの編集）から複雑なタスク（例：アーキテクチャ設計、アルゴリズム設計、証明）まで、段階的に分類することができます。推論の深さの推定は、[CLAUDE.md](CLAUDE.md)の「Reasoning Policy」のセクションに記載しています。

```markdown
## Reasoning Policy

Before responding to any request, first assess the required reasoning depth:

- **Simple** (e.g., factual lookup, single-file edit): Respond directly.
- **Moderate** (e.g., multi-file refactor, debugging): Think through the approach briefly before acting.
- **Complex** (e.g., architecture design, algorithm design, proof): Use extended reasoning — break the problem into sub-problems, consider trade-offs, then proceed step by step.

Always make your reasoning depth assessment explicit before responding:
> "This is a [simple/moderate/complex] task because ..."
```
