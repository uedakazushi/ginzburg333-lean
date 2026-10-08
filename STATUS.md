# 作業状況 — v5・両方向と同値の証明完了（2026年10月8日）

**元の二つの正則性の同値をLeanで証明しました。**

- 順方向: `Ginzburg333.tensorRegular_ginzburgRegular`
  （Comparison/Primitives.lean、標数0の代数閉体）。
- 逆方向: `Ginzburg333.ginzburgRegular_tensorRegular`
  （Converse/Main.lean、任意の体）。
- 同値: `Ginzburg333.ginzburgRegular_iff_tensorRegular`
  （Converse/Main.lean、標数0の代数閉体）。

TensorRegularとGinzburgRegularの元の意味を維持しています。
両述語と微分を定義するFinite/Coordinates.leanとGinzburg.leanは、
今回の開始HEADから一字も変更していません。avatar、sorry、admit、追加公理なし。
一般の独立した三つの三次元空間についても、実際のテンソル積基底と選択基底を介する逆方向・同値を実装しました。

## 今回の検証

作業ディレクトリ /workspace/ginzburg333-lean、ブランチwork、
開始HEAD 4a7657078a0af9ea51592bffc08988d135c4e2d9。
以前のWorkのプロセスを仮定せず、途中の実行環境再開後もGitと処理系を確認して実行しました。
Lean 4.19.0（6caaee842e94）、Lake 5.0.0、
mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b。

最終の `bash scripts/verify.sh` は終了0。
69数学モジュール、明示的theorem 540件、全公理監査1214件（生成定理を含む）、
Leanソース73件・7954行。両主定理と同値の型確認も成功。
依存公理はpropext、Classical.choice、Quot.soundのみです。
ログとVERIFICATION.jsonは今回の実行結果に基づいています。
CIと独立Python数値検査は今回は実行していません。

## 逆方向の完成箇所

1. LowDegree: 階数0の縮約から内部次数2の実際の負次数閉元を構成し、非完全性を導出。
2. Euler、Paths、Counting: 元のGinzburgRegularから実際の内部次数別完全性を得て、
   実際のJacobi商のEuler等式と頂点付き道の計数を証明。
   `2·finrank = 3(n+1)(n+2)`、内部次数36では2109次元。
3. Factors、Quotient: 階数1の縮約の因子分解、二つの直線を消す実際の商、
   全射な二次元関係商座標を構成。
4. Representation、MatrixRelations、WordMap、JacobiMap:
   2生成自由代数を係数とする行列表現を構成し、全生成元と有限支持の有効道で
   元の微分の像が零に写ることを証明。実際の内部Jacobi商へ写像を降ろしました。
5. LoopLifts、Growth: 自由語の実際の閉道への有限支持持ち上げを構成し、
   `2^m ≤ finrank (internalJacobi w (3*m))` を証明。
   m=12では4096以上となり、2109次元と矛盾します。
6. Main: 逆主定理、既存の順方向との同値、三つの基底・選択基底への接続。

FreeCornerDataは補助的な表現データです。主定理では階数1の因子分解から
その存在と指数下界を実際に証明して使っています。
下界や目的の結論を新しい仮定として置いていません。

## 順方向A〜Eと保存履歴

v4でA〜Eを完成しています。内部次数と包含+1付き短完全列、
頂点条件付き正規化自由行barの収縮、filtrationによる対角外完全性、
内部次数別有限双対と道複体の鎖同型、有限支持原始元と基底選択が実装済みです。
証明の入口はHANDOFF.mdを参照してください。

| 検証済み区切り | 全公理監査件数 |
|---|---:|
| 保存済みv3 | 561 |
| A | 630 |
| B〜C | 698 |
| A〜C・D部分 | 793 |
| 順方向完成v4 | 923 |
| 逆方向・多項式増大 | 1062 |
| 両方向・同値完成v5 | 1214 |

順方向完成4a7657078a0af9ea51592bffc08988d135c4e2d9と、
今回の増大度の区切り6718bd70f54bfa2c006cea24f82db8c5d114b8ebは実際にmainへ公開済み。
ユーザーは検証済み区切りのmainへのpushを明示承認済みです。
この完成版を含むコミットのSHAと公開状態はGit履歴とremote refで確認してください。
