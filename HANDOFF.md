# 引き継ぎ — v3 の正規化 bar 複体から内部次数と収縮へ

主定理は未宣言・未証明です。TensorRegular と GinzburgRegular の意味は維持しています。
Lean 4.19.0、mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b、固定 manifest を使用。
全31モジュール、明示的 theorem 272件がビルド済み。全561件の公理監査も成功。
scripts/verify.sh の終了コードは0。詳細は VERIFICATION.json にあります。

## 現在ある実体

- Ginzburg.FreeWords：語の積、Leibniz 則、符号作用、微分の二乗零。
- Ginzburg.SquareZero：道の有効性を忘れる単射を使った実際の道微分の二乗零。
- Ginzburg.Complex：有限次元の二重次数成分と微分。内部次数射影と有限和による原始元の組立て。
- Bar.Positive：21正次数基底、augmentation の核での展開、元の積の構造定数、結合則。
- Bar.Ambient：元の quotientAction を束ねた RightAction、有限支持の bar 語と自然性。
- Bar.InnerSquare / SquareZero：隣接因子と係数作用を合わせた実際の微分の二乗零。
- Bar.Homological：語長の成分、微分が長さを1減らすこと、各 r の有限次元性。
- Bar.Corners / Support：冪等元射影、合成可能な語、正規化射影、積の端点・重み。
- Bar.Normalized：正規化項、その実際の微分、二乗零、誘導鎖写像。
- Homology.Finsupp / Bar.NormalizedExact：自然な retract を用いる、各 r の実際の短完全列。

## 次の作業順

1. 商加群の quotientProjection d と wordWeight gs から内部次数 n の bar 部分空間を作る。
   d は Fin 4、総内部次数は d.val + wordWeight gs。
2. 元の係数作用が次数を足すことを示し、微分による内部次数保持を証明。
3. inclusion_degree (+1) と projection_degree (0) を実際の bar 写像へ移し、
   B_(r,n−1)(colon)→B_(r,n)(smaller)→B_(r,n)(U) の短完全列を作る。
4. 自由行加群の正規化 bar 複体の具体的な収縮を作る。
   ambient は k 上の語空間なので、そこだけで収縮を証明して S 上の結論に代用しない。
5. r=0 の正内部次数消滅と n<r の零を示し、filtration_induction を実際の bar 完全性へ適用。
6. 全空間商を e_i S と同定し、対角外消滅を得る。
7. 各 n の有限次元双対と Ginzburg の道空間の鎖同型を作る。
   比較符号だけでなく、因子の反転、頂点、生成元、微分の一致をすべて確認。
8. 内部次数ごとの原始元を得た後、ginzburgRegular_of_internal_primitives で有限和を戻す。
9. 三つの三次元空間の基底選択を接続し、主定理を宣言・証明。

## API 上の注意

normalizedTerm は normalization の像と lengthComponent r の共通部分。
normalizedDifferential は ambientDifferential の制限、normalizedMap は coefficientMap の制限。
filtration_normalized_short_exact は各 r の列であり、内部次数シフト付きではありません。

prependChain、tensorWords、coefficientMap の係数体 k が推論で曖昧になる場合は (k := k) を明示。
map_sum に線形写像を渡す場合は必要に応じて toAddMonoidHom を使います。
FreeWords の wordVectorDifferential_cons を simp に無条件登録すると単語 [g] でループします。
Support.lean は有限の頂点・生成元ケースをカーネルで検証するため、他のファイルよりコンパイルに時間がかかります。

## 再現と監査

通常の elan 環境では、展開したプロジェクトのルートで実行します。

    lake update
    lake exe cache get
    ./scripts/verify.sh

Linux の処理系未導入時は scripts/bootstrap.sh を使用できます。
readlink_compat.c は一部 PID namespace 環境の実行ファイル位置だけを補正します。
カーネルや証明検証の変更は行いません。

変更後は scripts/check_sources.py と scripts/verify.sh を実行。
AuditAll.lean は全 theorem の標準公理以外の依存を拒否します。
文字列監査・Python 検査を Lean 実行の代用にしないでください。
ソースとログを伴う checkpoint は source snapshot 全体を保存してください。
main_theorem_proved=false を維持し、未完の数学を追加公理で埋めないでください。

公開 Git リポジトリ、push、CI実行はありません。
