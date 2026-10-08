# 引き継ぎ — v4・A〜C完了からDの全長の微分比較へ

本来の主定理は未宣言・未証明。TensorRegularとGinzburgRegularの意味は維持。
今回の scripts/verify.sh 終了0。48数学モジュール、明示的theorem 383件、全公理監査793件。
Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b。詳細はVERIFICATION.jsonとlogs/。

## 完了した入口

Aの実際のB_(r,n)はBar/Internal.leanのinternallyNormalizedTerm。
内部次数は係数d.val+wordWeight。InternalDifferentialのinternalProjection_differentialで射影と微分が可換。
InternalExactのfiltration_internal_short_exactは包含の+1シフトを含む実際の短完全列です。

BはFree.leanのrowContractionとnormalizedRowContraction。
FreeHomotopyの基底計算を使ったFreeExactのrowContraction_homotopy_normalizedが
実際の頂点条件付きnormalizedTermでBH+HB=1を証明します。
FreeExactのinternally_normalized_free_exactは零部分空間商の各内部次数の完全性。

CはZero.leanのinternallyNormalized_zero_surjective（r=0,n>0）、
FiltrationのBarExact、barExact_filtration_step、normalized_bar_off_diagonal。
帰納法は実際の微分と実際の短完全列へ接続済み。一般の述語帰納で止まっていません。
Simple.leanは全空間商と頂点単純加群の同定、simple_normalized_bar_off_diagonalを提供します。

## 次の実装: D

- SimpleCoordinates: simpleBarCoordinatesEquivは実際の単純bar項とscalarSimpleTermの線形同型。
  SimpleDifferential: simpleScalarMap_differentialは実際の微分をinnerDifferentialへ移します。
- Comparison/FiniteDual: SimpleRowBasis、simpleBarLinearBasis、simpleBarDualCoordinatesと評価式。
  各(r,n)の有限双対です。全barの無限直積双対で代用していません。
- Comparison/Reversal: rowReversedBasisEquivは最初の頂点を保持して語を反転。
  wordSignは(-1)^Signs.sigma。finiteDualReversalは双対barからrowPathComponentへの線形同型。
  rowPathComponent_bigradedは実際のGinzburgの次数r−nを証明します。
- Comparison/Generators: generator_structure_coefficientは
  d[g]([h,t])=(-1)^(weight(t)+1)·positiveMultiplication(ofTensor w) t h g。
  生成元のみの比較です。全長比較は未証明。
- Comparison/Cobar: splitBasis、cobarBasis、cobarDifferential。
  cobarBasis_internal、cobarBasis_lengthは有限語の内部次数保存と語長+1。
  innerDifferentialの実際の転置との同定はまだありません。
- Comparison/DualExact: simple_dual_bar_off_diagonalは実際の制限微分のdualMapの完全性。

次は転置の係数式と全長の符号付き反転の可換性を実装してください。
必要な具体的結論はfiniteDualReversalがdualMapと実際のGinzburg制限微分を結ぶことです。
その結論を仮定として追加しないでください。
その後、頂点の有限直和、r=0端点、内部次数ごとの原始元、既存の有限和還元、一般の基底、主定理へ。

## 実行・保存

今回の処理系PATHは /workspace/.cloud-tooling/ginzburg333/lean-4.19.0-linux/bin。
次回そのパスや以前の実行プロセスがあると仮定せず、Git、lean --version、mathlib HEAD、ログを再確認。
verify.shは実行ビットが無いのでbash scripts/verify.sh。変更後にcheck_sources.pyとverify.shを実行。
source_auditはwork/以下の*.leanも走査するので、未検証の草稿は*.lean.txtとして保存。

Leanの型推論には(k := k)とExactAtのA/B/Cを明示すると有効です。
複雑な基底の評価式は、一般のbasisDualCoordinates_applyを作り、specialize時に
simp only [simpleBarDualCoordinates, basisDualCoordinates_apply]で書き換えると型変換の膨張を避けられます。
単純bar完全性を双対化する箇所ではBarExactとchainDifferential_succだけを先に展開します。

ユーザーはorigin uedakazushi/ginzburg333-leanのmainへの検証済み区切りのpushを明示承認済み。
Aのc6062b2a04a3378f3407bd339ae087a21b18375aは実際にmainへ公開済み。
GitHub connectorでtree、commit、expected_sha付きのforce=false update_refを使いました。
シェルのgit pushはセッションのproxy接続に失敗したためconnectorを使用。
次回もremote refを読み、現在のHEADを確認してから進めてください。CIは実行していません。
