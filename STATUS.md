# 作業状況 — v5・逆向き含意の実装中（2026年10月8日）

順方向の本来の主定理は証明済みです。今回追加された逆方向
`Ginzburg.GinzburgRegular w → TensorRegular w` は、現時点では未宣言・未証明です。

今回の開始HEADは4a7657078a0af9ea51592bffc08988d135c4e2d9、ブランチwork、作業ディレクトリ/workspace/ginzburg333-lean。
Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00bを再確認しました。
今回のverify.shは終了0。60数学モジュール、明示的theorem 472件、全公理監査1062件、Leanソース64件・7045行。標準の3公理以外の依存なし。

Converse/LowDegreeで階数0の縮約を実際の負次数閉元から除外しました。
Converse/Eulerで元のGinzburgRegularから実際の内部次数別完全性とJacobi商のEuler等式を導出。
Converse/Paths、Countingで頂点・次数を保つ有限基底の符号化と符号付き計数を証明し、
内部次数nのJacobi商について2·dim=3(n+1)(n+2)、特にn=36でdim=2109を証明しました。

階数1の場合には自由代数cornerへの写像と指数増大の下界を証明する必要があります。
この下界を仮定して逆主定理を宣言することはしていません。
以下は順方向を完成したv4の記録です。

# 作業状況 — 2026年10月8日 v4・主定理証明済み

**本来の主定理 `TensorRegular w → Ginzburg.GinzburgRegular w` をLeanで宣言・証明しました。**
`Ginzburg333.tensorRegular_ginzburgRegular`（Comparison/Primitives.lean）が入口です。
標数0の代数閉体上で要求された結論を満たします。avatarは使用せず、
TensorRegularとGinzburgRegularの定義、実際の有限支持道微分を維持しました。

今回の作業ディレクトリは `/workspace/ginzburg333-lean`、開始ブランチ `work`、開始HEAD
`9aeada1ce4b797b8be39e9c78e452cf21b2ea14f`。以前のWorkの実行状態は引き継いでいません。
Lean 4.19.0（6caaee842e94）、Lake 5.0.0、mathlib
c44e0c8ee63ca166450922a373c7409c5d26b00bを今回の環境で確認して実行しました。
基準verifyは終了0・全監査561件、Aの区切りは終了0・630件、
B〜Cのみの区切りは終了0・698件、D部分までの保存時点は終了0・793件でした。

最終の `bash scripts/verify.sh` は終了0。56数学モジュール、明示的theorem 433件、全公理監査923件（生成定理を含む）、Leanソース60件・6451行。
主定理の型確認と公理監査も実行済み。sorry・admit・追加公理なし。
依存公理はpropext、Classical.choice、Quot.soundのみです。
logs/とVERIFICATION.jsonは今回の実行結果です。CIと独立数値検査は今回は実行していません。

## A〜Eの完成箇所

- A: Bar/Internal、InternalDifferential、InternalExact。
  係数次数と語の重みによる内部次数、実際の微分との可換射影、有限次元性、n<rの零。
  包含の次数+1を反映した内部次数別短完全列と微分の両立。
- B: Bar/Free、FreeHomotopy、FreeExact。
  頂点条件付きの実際の正規化自由行bar上で収縮を構成し、正の語長でBH+HB=1。
- C: Bar/Zero、Filtration、Simple。
  r=0,n>0の消滅、実際の短完全列のdiagram chase、filtration帰納法。
  Allowedな商行と頂点単純加群の実際の正規化barの対角外完全性。
- D: Comparison/FiniteDual、Reversal、Generators、Transpose、WordReversal、FiniteChain、Total。
  各(r,n)の有限次元双対と有効道成分を符号付き因子反転で同定。
  頂点、生成元係数、全長の符号、実際の微分の両立を証明。
  finiteDualReversal_differentialとtotalDualReversal_differentialが実際の鎖同型を与えます。
  totalDualReversalは三頂点の有限双対の直和とGinzburgの二重次数成分全体の同型です。
- E: Comparison/Primitives、Bases。
  実際の双対bar完全性から内部次数別の原始元を構成し、有限支持の有限和へ戻しました。
  任意の独立した三つの三次元空間のテンソル積基底と基底選択を接続。
  tensorRegular_ginzburgRegularが本来の主定理です。

`ginzburgRegular_of_internal_primitives`自体は条件付き還元補題です。
今回はその仮定をginzburg_internal_primitivesで証明し、主定理へ適用しました。
結論を含む仮定によって主定理を補っていません。

originはuedakazushi/ginzburg333-lean。ユーザーは検証済み区切りのmainへのpushを明示承認しました。
Aのc6062b2a04a3378f3407bd339ae087a21b18375aと、B〜C・D部分の69e7c880d2cdbbe6d7e40cce3eb4dc4cd52f075aは
実際にmainへpushし、参照確認済みです。この完成版も同じmainへの公開対象です。
このファイルを含む完成コミットの公開状態・SHAはGit履歴とremote refで確認してください。
