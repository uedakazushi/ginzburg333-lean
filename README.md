# Ginzburg (3,3,3)：avatar を用いない Lean 形式化 — v3

**主定理「テンソル正則 ⇒ Ginzburg正則」はまだ未証明です。**
この版では、有限支持の実際の Ginzburg 微分の二乗零と、正規化 bar 複体の項・微分・二乗零・自然性・短完全列まで形式化しました。
全31モジュール、272件の明示的 theorem 宣言がビルドを通り、生成補助定理を含む561件の公理監査も成功しています。
検証結果と件数は STATUS.md と VERIFICATION.json、残る数学は GAPS.md、再開の順序は HANDOFF.md にあります。

目標は、標数0の代数閉体と三次ポテンシャル w について

    TensorRegular w → Ginzburg.GinzburgRegular w

を証明することです。TensorRegular は三方向の非零縮約の階数が2以上、
GinzburgRegular は有限支持の道空間の負次数閉元が境界であることです。
この意味を別の証明書や消滅仮定に変更していません。

## 検証済みの構成

| ファイル群 | 内容 |
|---|---|
| Finite、Auxiliary | 縮約・階数・colon、24次元補助代数、実際の商加群、filtration と短完全列 |
| Homology、Signs | 図式追跡、双対・有限支持への完全性の移送、一般帰納法、比較符号 |
| Ginzburg、Words、Homogeneous、FiniteDegree | 道と微分、端点・次数、内部次数成分の有限次元性 |
| Ginzburg/FreeWords、SquareZero、Complex | Leibniz 則、実際の微分の d²=0、二重次数成分、有限和による原始元の組立て |
| Bar/Positive、Ambient、InnerSquare、SquareZero | 実際の補助代数と商作用を使う有限支持 bar 微分と二乗零 |
| Bar/Homological、Corners、Support、Normalized | 語長と頂点条件、正規化射影、実際の正規化微分と自然性 |
| Bar/NormalizedExact | 各ホモロジー次数の正規化項の短完全列 |

bar の内部次数 n の部分空間、自由行加群の収縮、帰納法による対角外消滅、
bar と Ginzburg の有限次数双対の鎖同型、最後の主定理は残っています。
一般帰納法や比較符号の補題だけで消滅を証明したとは扱いません。

## 再現

Lean 4.19.0、mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b を固定。
依存パッケージは lake-manifest.json にあります。
通常の elan 環境でプロジェクトのルートから実行してください。

    lake update
    lake exe cache get
    ./scripts/verify.sh

Linux の処理系未導入環境には scripts/bootstrap.sh を用意しました。
検証スクリプトは全モジュールと Audit.lean、AuditAll.lean を実行します。
AuditAll は名前空間内の全 theorem について標準公理以外を拒否します。
追加公理、sorry、admit、native_decide、unsafe による証明は使用しません。

直接証明ノートと原論文は docs/ に同梱しています。
前版の独立 Python 検査は保持していますが、Lean 検証の代用にはしません。
