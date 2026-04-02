# Lessons Learned

このプロジェクトを進める中で得られた洞察や学びをまとめます。

## `gpow_add`の証明でトークン制限に達した

整数指数の加法性を証明する`gpow_add`をClaude Codeに証明させようとしましたが、証明が複雑だったためか、トークン制限に達して証明が完了しませんでした。

補題`gpow_add`は、以下のようになります。

```
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
