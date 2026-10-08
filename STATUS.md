# 作業状況 — 2026年10月8日 v4・A

**本来の主定理 TensorRegular w → Ginzburg.GinzburgRegular w は未宣言・未証明です。**
Aの内部次数と次数シフト付き短完全列を実装しました。TensorRegular、GinzburgRegularの定義は変更していません。

今回の作業環境は `/workspace/ginzburg333-lean`、開始ブランチは `work`、開始HEADは `9aeada1ce4b797b8be39e9c78e452cf21b2ea14f`。
GitHub `uedakazushi/ginzburg333-lean` の `main` も開始時に同じHEADでした。
v3記録の作業パスや以前のWorkの実行状態は引き継いでいません。
PATHに既存の `/workspace/.cloud-tooling/ginzburg333/lean-4.19.0-linux/bin` を指定し、
Lean 4.19.0、Lake 5.0.0、mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b を実際に確認しました。

基準の scripts/verify.sh は終了コード0、561件の全公理監査を通過しました。
Aの検証は scripts/verify.sh 終了コード0、34数学モジュール、明示的theorem 308件、全公理監査630件。
Leanソース38件・4280行。追加公理・sorry・admitなし、公理依存は propext、Classical.choice、Quot.sound のみ。
今回のログ・ソース在庫は logs/、機械可読記録は VERIFICATION.json にあります。
Pythonの独立数値検査は今回実行していません。

## 検証済みの追加

- Bar/Internal.lean: 係数の四次数射影と wordWeight を合わせた内部次数。
  元の係数作用が生成元の重みを加えること、頂点射影との両立、実際の正規化部分空間 B_(r,n)、
  微分の内部次数保存・二乗零・各成分の有限次元性。
- Bar/InternalDifferential.lean: 内部次数射影と実際のbar微分の可換性、n<rの成分が零であること。
- Bar/InternalExact.lean: 包含の内部次数+1を反映した
  B_(r,n)(colon) → B_(r,n+1)(smaller) → B_(r,n+1)(U) の単射・像=核・全射。
  包含と商写像の微分との両立。頂点条件と有限支持を維持しています。

Bの収縮恒等式、r=0,n>0の消滅、Cの実際のfiltration帰納、Dの鎖同型、Eの主定理は残ります。
一般の帰納補題や条件付きの原始元還元を主定理の完成とは扱いません。
GitHub pushの今回の結果は、この区切りの保存後に記録します。CIは実行していません。
