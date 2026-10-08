# 作業状況 — 2026年10月8日 v3

**主定理「テンソル正則 ⇒ Ginzburg正則」は引き続き未証明です。**
今回、有限支持の実際の Ginzburg 微分の二乗零と、正規化 bar 複体の微分・自然性・短完全列を追加しました。
全31数学モジュールがビルドに成功し、明示的な theorem 宣言272件を検証しました。
生成補助定理を含む561件の公理監査も通りました。終了コードはすべて0です。

| 項目 | 最終結果 |
|---|---|
| Lean / mathlib | 4.19.0 / c44e0c8ee63ca166450922a373c7409c5d26b00b |
| 数学用モジュール | 31件、すべてビルド成功 |
| 明示的 theorem 宣言 | 272件、うち今回追加135件 |
| Lean ファイル全体 | 35件、3751行 |
| scripts/verify.sh | 成功、終了コード0 |
| Audit.lean | 主要28件の公理を表示、成功 |
| AuditAll.lean | 561件を監査、成功 |
| 公理依存 | propext、Classical.choice、Quot.sound のみ |
| 追加公理・sorry・admit | なし |
| 主定理 | 未宣言・未証明 |

実行記録は VERIFICATION.json と logs/ にあります。

## 今回の数学的な進捗

1. `Ginzburg/FreeWords.lean`：有限支持の語空間上の積と符号作用を構成。
   微分の Leibniz 則、符号作用との反可換性、生成元と任意語での二乗零を証明。
2. `Ginzburg/SquareZero.lean`：道の有効性を忘れる単射を介して、既存の実際の道空間上の微分について `differential_square` を証明。
   微分や目標述語の定義を別の証明書に置き換えていません。
3. `Ginzburg/Complex.lean`：内部次数 n とコホモロジー次数 q の有限次元成分、実際の成分微分と二乗零。
   内部次数射影と微分の可換性、有限支持の内部次数成分から原始元を有限和で戻す補題を証明。
   この最後の補題は成分ごとの原始元の存在を仮定する還元補題であり、消滅を証明したものではありません。
4. `Bar/Positive.lean`：正次数の21個の基底、augmentation の核での展開、実際の補助代数から得る構造定数と結合則。
5. `Bar/Ambient.lean`、`InnerSquare.lean`、`SquareZero.lean`：既存の `QuotientRow` の右作用を使う有限支持の bar 語と微分。
   隣接因子の積と最初の係数作用を合わせた微分の二乗零、加群写像への自然性。
6. `Bar/Homological.lean`、`Corners.lean`、`Support.lean`：語長による成分、各成分の有限次元性、頂点冪等元、合成可能性、正規化射影。
   積の非零係数が端点と内部重みを保つこと。正規化は S=k³ 上のテンソルの頂点条件を明示的に実装しています。
7. `Bar/Normalized.lean`：微分が正規化部分を保つこと、実際の正規化微分、その二乗零、誘導された鎖写像。
8. `Homology/Finsupp.lean`、`Bar/NormalizedExact.lean`：有限支持への完全性の移送と自然な正規化・語長射影による retract。
   `FiltrationStep.short_exact` から、各ホモロジー次数の正規化 bar 項の単射・像=核・全射を証明。

## 残る数学

正規化 bar 項にはまだ内部次数 n の部分空間を実装していません。
したがって短完全列は現在、ホモロジー次数 r ごとの列です。
包含写像の内部次数 +1 を反映した n−1→n の短完全列は次の作業です。

自由行加群での bar 収縮、r=0 の正内部次数消滅、対角外消滅への二重帰納法の適用、
bar の有限次数双対と Ginzburg 道複体の鎖同型、主定理が残ります。
Ginzburg 側の d²=0 は今回解決しています。

## 検証と再現

Lean 4.19.0 と mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b を固定。
`scripts/verify.sh` は全モジュールをビルドし、選択した主要定理と名前空間内の全 theorem の公理を監査します。
標準公理 propext、Classical.choice、Quot.sound 以外は拒否します。
ソースの文字列監査はコンパイル・公理監査とは区別します。

前版の独立 Python 検査は保存していますが、今回再実行したとは扱いません。
GitHubへの公開・push、CI実行は行っていません。
詳細は GAPS.md、再開の入口は HANDOFF.md を参照してください。
