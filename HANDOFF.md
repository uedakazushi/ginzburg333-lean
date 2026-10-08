# 引き継ぎ — v7・GitHub Pages CI

.github/workflows/blueprint-pages.ymlが入口です。
全体verify、blueprintのPDF/HTML生成・実際の宣言検査、公開パッケージ作成の順に進みます。
成功したmainのartifactをpages:write・id-token:write付きの別jobでデプロイします。
pull requestはデプロイしません。処理系・mathlib・Python依存の固定は維持しています。
scripts/package_blueprint_pages.pyは.tooling/pagesを作り、/ginzburg333-lean/以下の相対リンクを検査します。
PDFへの入口も追加し、実行リビジョンと検証済み数学ソースの保存点をsite-build.jsonに記録します。

所有者がPagesのSourceをGitHub Actionsに設定済みで、APIでhas_pages=trueを確認しました。
初回run 37736611956はリポジトリ内の処理系ソースを字句監査が走査して失敗しました。
修正版ではGINZBURG333_TOOLINGをrunner.temp以下に置きます。監査スクリプトの対象は狭めていません。
次のrun 37737108544ではverify.shと1214件の公理監査が成功し、TeXのpzdr.tfm不足で文書生成が失敗しました。
texlive-fonts-recommendedを追加しています。verify/build/deployを別jobに分け、
文書だけの再実行では成功済みLean jobをやり直さず、そのcacheを復元する構成です。
実際のCI結果と公開URLの取得が成功するまでは、デプロイ完了と記録しないでください。
公開先は https://uedakazushi.github.io/ginzburg333-lean/ 、PDFは同URLのblueprint_ja.pdfです。
Actionsのworkflow/jobログとPagesのHTTP・ブラウザ検査を保存してSTATUS/GAPS/VERIFICATIONを更新してください。

今回の数学的Leanソースは変更していません。v6のLean・blueprintの検証結果は維持されています。

以下はv6の引き継ぎです。

# 引き継ぎ — v6・日本語 Lean blueprint付き

数学的な両主定理・同値は完成したままです。Leanソースへの変更はありません。
日本語の入口はblueprint/README.md、本文はblueprint/src/content.tex、
公開成果物はblueprint/web/とblueprint/print/print.pdfです。

標準leanblueprint 0.0.20で51項目、103件のLean宣言、118本の数学的依存辺を記述。
blueprint/declarations.jsonは保存点ea11e52179e60a9a64b673f43538a8a448e23b74の実際のソース行へ対応させています。
scripts/build_blueprint.py、scripts/check_blueprint.pyで再生成・検査してください。
固定されたLean依存を変えず、宣言検査はlake env lean --stdinで実行します。
MathJaxとフォント、グラフの資源はHTMLと同梱しています。
HTTPでの閲覧方法と文書処理系の準備はblueprint/README.mdを参照してください。

今回の全体verifyは終了0・1214件公理監査。文書生成、103宣言のLean検査、
日本語PDF10ページ、HTML14ページの1142内部参照、51ノードのブラウザ操作が成功しました。
blueprint/verification.json、logs/blueprint_browser.jsonとVERIFICATION.jsonは今回の実行結果です。
数学ソースを変えた場合はblueprint/source_commit.txtと対応表を適切に更新する必要があります。
生成物のSHAとソースハッシュを検査記録に保存しています。

ユーザーはこのリポジトリとblueprintの公開を明示指示し、mainへのpushも承認済み。
blueprintを含むmain保存点はc0380df5bc1bc6a14eda856a958d826d9a6625d6です。
GitHub APIでツリーb42c4efb1ca449c1a7c799620bf8a3a76a039da7と親ea11e52179e60a9a64b673f43538a8a448e23b74を確認済み。
この記録を加えた後続コミットのSHAはGit履歴とremote refを確認してください。CIは今回未実行です。
所有者の設定変更後、2026年10月8日06:01 UTCにvisibility=public、private=falseをAPIで確認しました。
mainのb3398d8a44d16e7dc8e6098ed99747a2bd317885を確認し、認証なしでもblueprint入口・PDF・HTML・
Converse/Main.leanがHTTP 200で取得でき、検証済みローカルファイルとSHA-256が一致しました。
一般公開は完了です。実行記録はlogs/publication_checks.jsonとVERIFICATION.jsonにあります。
GitHub Pagesは未設定（has_pages=false）です。HTMLの閲覧方法はblueprint/README.mdを参照してください。
以前のWorkのプロセスが残ると仮定せず、再開時にGitと処理系を確認してください。

以下は両方向完成時のv5の数学的引き継ぎです。

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
