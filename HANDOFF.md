# 引き継ぎ — v4・要求された主定理まで完成

入口は `Ginzburg333/Comparison/Primitives.lean` の
`Ginzburg333.tensorRegular_ginzburgRegular`。
元のTensorRegularから元のGinzburgRegularを証明しています。avatarは使用しません。
A〜Eは完成。`bash scripts/verify.sh`終了0。56数学モジュール、明示的theorem 433件、全公理監査923件（生成定理を含む）、Leanソース60件・6451行。
Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b。
詳細はVERIFICATION.json、logs/、STATUS.md、GAPS.mdにあります。

## 証明の入口と依存関係

1. Bar/InternalのinternallyNormalizedTermが実際のB_(r,n)。
   InternalDifferentialのinternalProjection_differentialが次数保存、
   InternalExactのfiltration_internal_short_exactが包含+1付きの実際の短完全列。
2. Free、FreeHomotopy、FreeExactで正規化自由行収縮を構成。
   rowContraction_homotopy_normalizedは頂点条件付きの実際の項でBH+HB=1。
   ZeroのinternallyNormalized_zero_surjectiveがr=0,n>0の基底消滅。
3. FiltrationのbarExact_filtration_stepとnormalized_bar_off_diagonalが実際の帰納法。
   Simpleのsimple_normalized_bar_off_diagonalが頂点単純barの完全性。
4. SimpleCoordinates、SimpleDifferentialで実際のbar微分をスカラー化。
   FiniteDual、Reversalで各(r,n)の有限双対から頂点付き道への符号付き線形同型。
   Generatorsのgenerator_structure_coefficientが元のテンソルによる係数の一致。
   TransposeのcobarBasis_transposeとWordReversalのsignedWordReversal_differentialが
   全長の転置と符号を処理。FiniteChainのfiniteDualReversal_differentialが鎖同型。
   TotalのtotalDualReversalとtotalDualReversal_differentialが三頂点を合成。
5. DualExactのsimple_dual_bar_off_diagonalをPrimitivesのrowPath_primitiveに適用。
   ginzburg_internal_primitives、既存の有限和還元、主定理の順に接続。
   BasesのtensorCoordinatesEquivとchosenTensorCoordinatesが一般の三つの三次元空間との接続。

## 再検証と保存

次回もGit、処理系、mathlib HEAD、ログを確認し、以前のプロセスが残るとは仮定しないでください。
今回の処理系PATHは `/workspace/.cloud-tooling/ginzburg333/lean-4.19.0-linux/bin`。
通常は固定されたlean-toolchainとlake-manifest.jsonの環境で以下を実行します。

    python3 scripts/check_sources.py
    bash scripts/verify.sh

verify.shは実行ビットがありません。Audit.leanは主定理の型も確認し、
AuditAll.leanは生成定理を含む名前空間内の全theoremの依存公理を検査します。
source_auditは字句検査のみで、Lean検証の代用にはしません。
work/以下の*.leanも走査するので草稿は*.lean.txtに保存します。

複雑な基底座標では一般の評価式を使い、実際の基底ごとの展開を抑えると有効です。
有限双対基底の等式はrepr_selfの型変換より評価でextする方が安定します。

ユーザーはorigin uedakazushi/ginzburg333-leanのmainへの検証済み区切りのpushを明示承認済み。
この完成版の親は、実際に公開済みの69e7c880d2cdbbe6d7e40cce3eb4dc4cd52f075aです。
GitHub connectorでtree、commit、expected_sha付きのforce=false update_refを使用できます。
シェルgit pushはセッションproxy接続に失敗したためconnectorを使用しました。
公開済みSHAとremote refは次回も実際に読み取って確認してください。CIは今回実行していません。
