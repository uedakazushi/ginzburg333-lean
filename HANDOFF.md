# 引き継ぎ — v5・両方向と同値を完成

入口は `Ginzburg333/Converse/Main.lean`。
元の述語に対する逆主定理 `ginzburgRegular_tensorRegular` は任意の体上で成立します。
`ginzburgRegular_iff_tensorRegular` は標数0の代数閉体上の同値です。
順方向はComparison/Primitives.leanの `tensorRegular_ginzburgRegular`。
avatarは使用していません。要求されたA〜Eと逆方向は完了です。

今回の最終verify.shは終了0。69数学モジュール、明示的theorem 540件、
全公理監査1214件、Leanソース73件・7954行。標準3公理以外の依存なし。
現在の状態はSTATUS.md、GAPS.md、VERIFICATION.json、logs/を参照してください。
草稿と過去の中間ログはwork/以下にあり、完成したLeanソースの代用ではありません。

## 逆方向の依存関係

1. LowDegreeのginzburgRegular_contraction_ne_zeroは、内部次数2の実際の閉元で階数0を排除。
2. EulerのinternalJacobiは実際のbigradedComponent n 0を実際の制限微分の像で割った商。
   negativeDifferential_exactは元のGinzburgRegularから内部次数ごとの負次数完全性を導出。
3. Pathsは有効道と頂点・重み付き語の同値、Countingは符号付き計数と有限Euler和を処理。
   internalJacobi_quadratic_growth、internalJacobi_finrank_36により内部次数36の実際の商は2109次元。
4. FactorsのrankOneSlice_of_not_regularとQuotientのfreeCornerData_existsは、
   階数1の因子分解と実際の二つの直線商から全射な二次元出力を構成。
5. RepresentationとMatrixRelationsは自由代数係数の4×4行列表現と全巡回関係の消滅。
   WordMapは頂点条件付き閉語を実際の有効道へ送ります。
   JacobiMapのpathMatrixEvaluation_differentialは元の道微分全体を零に送り、
   jacobiEvaluationを実際の内部Jacobi商上に定義します。
6. LoopLiftsのliftFreeWord_entry00は有限支持閉道の像が対応する自由語であることを証明。
   GrowthのfreeCorner_exponential_lower_boundはその像の独立性から2^mの下界を証明。
7. Mainでm=12、内部次数36に適用して4096≤2109の矛盾。
   逆主定理、同値、任意の三つの基底と選択基底への接続を宣言・証明。

FreeCornerDataやLoopLiftDataは実際の有限支持の構成を記録する補助データです。
存在と下界を目的の仮定から証明済みです。条件付き還元だけを主定理と呼んでいません。

## 順方向A〜Eの依存関係

1. Bar/Internal、InternalDifferential、InternalExact:
   実際の内部次数項、射影と微分の可換性、包含の+1を反映した短完全列。
2. Free、FreeHomotopy、FreeExact:
   頂点条件付きの正規化自由行barでBH+HB=1。
   ZeroのinternallyNormalized_zero_surjectiveがr=0,n>0の基底消滅。
3. FiltrationのbarExact_filtration_step、normalized_bar_off_diagonalと
   Simpleのsimple_normalized_bar_off_diagonalが実際の対角外完全性。
4. SimpleCoordinates、SimpleDifferential、FiniteDual、Reversal、Generators、
   Transpose、WordReversal、FiniteChain、Total:
   因子反転、頂点、生成元係数、符号、全長の実際の微分と両立する有限双対の道同型。
   finiteDualReversal_differentialとtotalDualReversal_differentialが入口。
5. DualExact、Primitives:
   rowPath_primitive、ginzburg_internal_primitives、有限和還元、主定理の順に接続。
   BasesのtensorCoordinatesEquivとchosenTensorCoordinatesは独立した三空間の実際の基底座標です。

## 再検証とGit

次回もGit、処理系、mathlib HEAD、ログを実際に確認し、
前回のWorkや途中の実行環境再開前のプロセスが残るとは仮定しないでください。
今回の処理系PATHは /workspace/.cloud-tooling/ginzburg333/lean-4.19.0-linux/bin。
Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00bを固定しています。

    python3 scripts/check_sources.py
    bash scripts/verify.sh

verify.shは実行ビットがありません。Audit.leanは両主定理と同値の型も確認し、
AuditAll.leanは生成定理を含む名前空間内の全theoremの依存公理を検査します。
source_auditは字句検査のみ。work/以下の*.leanも走査するので草稿は*.lean.txtに保存します。

今回の開始HEADは4a7657078a0af9ea51592bffc08988d135c4e2d9、
増大度の公開済み区切りは6718bd70f54bfa2c006cea24f82db8c5d114b8eb。
完成版の公開状態とSHAはGit履歴とmainのremote refで確認してください。
ユーザーはorigin uedakazushi/ginzburg333-leanのmainへの検証済み区切りのpushを明示承認済み。
GitHub connectorのtree、commit、expected_sha付きforce=false update_refで公開できます。
CIは今回実行していません。
