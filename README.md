# Ginzburg (3,3,3)：avatarを用いないLean形式化 — v4

**標数0の代数閉体上で `TensorRegular w → Ginzburg.GinzburgRegular w` を証明しました。**
主定理は `Ginzburg333.tensorRegular_ginzburgRegular`、
ソースは [Comparison/Primitives.lean](Ginzburg333/Comparison/Primitives.lean)です。
TensorRegularは三方向の非零縮約の階数が2以上、GinzburgRegularは
実際の有限支持道空間の負次数閉元が境界であることです。元の意味を維持しています。

今回の全体検証は終了0。56数学モジュール、433件の明示的theorem宣言、
生成定理を含む923件の公理監査が成功しました。
依存公理はpropext、Classical.choice、Quot.soundのみ。
結果はSTATUS.mdとVERIFICATION.json、証明の入口はHANDOFF.mdにあります。

## 証明の構成

| 段階 | 実装 |
|---|---|
| A | Bar/Internal、InternalDifferential、InternalExact：係数次数と語の重み、実際の微分の次数保存、包含+1付き短完全列 |
| B | Bar/Free、FreeHomotopy、FreeExact：頂点条件付き正規化自由行barの収縮とBH+HB=1 |
| C | Bar/Zero、Filtration、Simple：基底消滅、実際の短完全列の帰納法、対角外完全性 |
| D | Comparison/以下：有限次元双対、符号付き因子反転、生成元と全長微分の両立、実際の道複体との鎖同型 |
| E | Comparison/Primitives、Bases：有限支持原始元、三つの三次元空間の基底選択、本来の主定理 |

条件付き還元補題ginzburgRegular_of_internal_primitivesの仮定は、今回の実際のbar比較から証明しました。
一般の三つの独立した空間には、実際のテンソル積基底の座標同型を介して主定理を適用します。

## 再現

Lean 4.19.0、mathlib c44e0c8ee63ca166450922a373c7409c5d26b00bを固定。
依存パッケージはlake-manifest.jsonに記録しています。
固定された処理系と依存を用意したプロジェクトのルートで実行してください。

    python3 scripts/check_sources.py
    bash scripts/verify.sh

Linuxの処理系未導入環境にはscripts/bootstrap.shを用意しました。
検証スクリプトは全モジュール、Audit.lean、AuditAll.leanを実行します。
主定理の型を確認し、名前空間内の全theoremについて標準公理以外を拒否します。
追加公理、sorry、admit、native_decide、unsafeによる証明は使用しません。

直接証明ノートと原論文はdocs/に同梱しています。
前版の独立Python検査は保持していますが、Lean検証の代用にはしません。
