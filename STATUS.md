# 作業状況 — 2026年10月8日 v4・A〜CとDの部分実装

**本来の主定理 TensorRegular w → Ginzburg.GinzburgRegular w は未宣言・未証明です。**
A〜Cは実際の頂点条件付き正規化barで完了しました。Dは有限双対と符号付き線形同型、生成元係数まで。
全長の微分可換性と鎖同型、Eの主定理は残っています。TensorRegularとGinzburgRegularの定義は維持。

今回の作業ディレクトリは `/workspace/ginzburg333-lean`、開始ブランチ `work`、開始HEAD
`9aeada1ce4b797b8be39e9c78e452cf21b2ea14f`。以前のWorkの実行状態は引き継いでいません。
Lean 4.19.0（6caaee842e94）、Lake 5.0.0、mathlib
c44e0c8ee63ca166450922a373c7409c5d26b00b を今回の環境で確認して実行しました。
基準verifyは終了0・全監査561件、Aの区切りは終了0・630件、B〜Cの区切りは終了0・698件。

このソースの scripts/verify.sh は終了0。48数学モジュール、明示的theorem 383件、
全公理監査793件（生成定理を含む）、Leanソース52件・5665行。
sorry・admit・追加公理なし。依存公理は propext、Classical.choice、Quot.sound のみ。
logs/とVERIFICATION.jsonは今回の実行結果です。独立数値検査やCIは今回は実行していません。

## 検証済みの内容

- A: Bar/Internal、InternalDifferential、InternalExact。
  係数degreeと語の重みの和による内部次数、実際の微分との可換射影、有限次元性、n<rの零。
  包含の次数+1を反映した短完全列と微分の両立。
- B: Bar/Free、FreeHomotopy、FreeExact。
  正次数係数を先頭へ移す収縮、頂点条件の保存、正の語長でBH+HB=1。
  正規化された自由行加群とその零部分空間商での完全性。
- C: Bar/Zero、Filtration、Simple。
  r=0,n>0の消滅、実際の次数付き短完全列へのdiagram chase、filtration帰納法。
  Allowedな全商行のn≠rでの実際のbar完全性。全空間商と頂点単純加群の同定。
- Dの部分成果: Bar/PathBasis、SimpleCoordinates、SimpleDifferential、Comparison/以下。
  正規化bar項のスカラー座標と実際の微分の両立、各(r,n)の有限基底と双対座標、
  符号付き因子反転による頂点付き有効道成分への線形同型、r−nの次数関係。
  元のテンソルによる生成元微分と補助代数の積の構造定数・符号の一致。
  実際の有限次数双対barの対角外完全性。cobarの有限語の重み保存と語長+1。

finiteDualReversalは現段階では線形同型です。微分可換性を仮定して主定理を埋めていません。
ginzburgRegular_of_internal_primitivesは既存の条件付き還元であり、主定理ではありません。

originは uedakazushi/ginzburg333-lean。ユーザーは検証済み区切りのmainへのpushを明示承認しました。
Aの区切り c6062b2a04a3378f3407bd339ae087a21b18375a は実際にmainへpushし、参照も確認済み。
この区切りの公開先も同じmainです。実際のコミットと参照はGit履歴で確認してください。
