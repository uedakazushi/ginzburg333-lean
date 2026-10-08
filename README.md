# Ginzburg (3,3,3)：avatarを用いないLean形式化 — v5・同値証明済み

**標数0の代数閉体上で `Ginzburg.GinzburgRegular w ↔ TensorRegular w` をLeanで証明しました。**

- 順方向: `Ginzburg333.tensorRegular_ginzburgRegular`
  ([Comparison/Primitives.lean](Ginzburg333/Comparison/Primitives.lean))。
- 逆方向: `Ginzburg333.ginzburgRegular_tensorRegular`
  ([Converse/Main.lean](Ginzburg333/Converse/Main.lean))。逆方向は任意の体上で成立します。
- 同値: `Ginzburg333.ginzburgRegular_iff_tensorRegular`
  ([Converse/Main.lean](Ginzburg333/Converse/Main.lean))。

TensorRegularは三方向の非零縮約の階数が2以上、GinzburgRegularは
実際の有限支持道空間の負次数閉元が境界であることです。元の意味を維持しています。
一般の独立した三つの三次元空間には、実際のテンソル積基底の座標同型を介して適用します。

最終全体検証は終了0。69数学モジュール、540件の明示的theorem宣言、
生成定理を含む1214件の公理監査が成功しました。
依存公理はpropext、Classical.choice、Quot.soundのみ。
結果はSTATUS.mdとVERIFICATION.json、証明の入口はHANDOFF.mdにあります。

## 証明の構成

| 段階 | 実装 |
|---|---|
| A | Bar/Internal、InternalDifferential、InternalExact：内部次数、実際の微分の次数保存、包含+1付き短完全列 |
| B | Bar/Free、FreeHomotopy、FreeExact：頂点条件付き正規化自由行barの収縮とBH+HB=1 |
| C | Bar/Zero、Filtration、Simple：基底消滅、短完全列とfiltrationの帰納法、対角外完全性 |
| D | Comparison/以下：有限双対、符号付き因子反転、生成元と全長微分の両立、実際の道複体との鎖同型 |
| E | Comparison/Primitives、Bases：有限支持原始元、三次元空間の基底選択、順主定理 |
| 逆方向 | Converse/以下：実際のJacobi商の多項式増大、階数1からの自由語持ち上げによる指数下界、次数36の次元矛盾 |
| 同値 | Converse/Main：両主定理の接続、三つの基底・選択基底への接続 |

内部次数別原始元の存在も指数下界も、本来の入力から証明済みです。
条件付き還元補題の仮定を新しい主定理の仮定として置いていません。

## 再現

Lean 4.19.0、mathlib c44e0c8ee63ca166450922a373c7409c5d26b00bを固定。
依存パッケージはlake-manifest.jsonに記録しています。
固定された処理系と依存を用意したプロジェクトのルートで実行してください。

    python3 scripts/check_sources.py
    bash scripts/verify.sh

Linuxの処理系未導入環境にはscripts/bootstrap.shを用意しました。
検証スクリプトは全モジュール、Audit.lean、AuditAll.leanを実行します。
両主定理と同値の型を確認し、名前空間内の全theoremについて標準公理以外を拒否します。
追加公理、sorry、admit、native_decide、unsafeによる証明は使用しません。

直接証明ノートと原論文はdocs/に同梱しています。
前版の独立Python検査は保持していますが、今回は再実行しておらず、Lean検証の代用にもしていません。
