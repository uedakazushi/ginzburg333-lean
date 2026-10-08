# 未完了部分 — v4・A〜C完了、D部分実装

**本来の主定理は未証明。追加公理や結論を含む仮定による補完はありません。**
今回の scripts/verify.sh は終了0、明示的theorem 383件、全公理監査793件。

## G1–G3: 補助代数・商加群・内部次数付きbar — A完了

元の24次元補助代数、21正次数基底、商作用、colonとfiltrationを維持。
頂点と係数の最初の頂点射影を課した正規化bar、内部次数付き項・微分・二乗零、
有限次元性、次数射影との可換性、包含次数+1付き短完全列を実装済み。

## G4: 正規化自由収縮・基底消滅・filtration — B〜C完了

自由行の正次数部分を先頭因子へ移す収縮は、実際のnormalizedTerm上で
頂点条件を保ち、正の語長でBH+HB=1を満たします。ambient複体で代用していません。
零部分空間商の内部次数別完全性、r=0,n>0の消滅、n<rの項の零、
実際の複体と実際の短完全列によるdiagram chaseとfiltration帰納を接続済み。
normalized_bar_off_diagonalはD.RegularとD.Allowedから実際のBarExactを証明します。
全空間商とe_i Sの同定も完了。内部次数0のTor_0を零とする仮定はありません。

## G5: Ginzburg道微分 — 実体を維持

実際の有限支持道微分、二乗零、次数保存、有限次元成分、内部次数の有限和還元は維持。
負次数消滅は未証明。

## G6: bar/Ginzburg鎖同型 — 未完了

各(r,n)の実際の頂点単純bar項の有限基底と双対座標、符号付き因子反転による
有効道成分への線形同型finiteDualReversal、頂点と次数r−nの対応は実装済み。
単純barの座標化が微分をinnerDifferentialへ移すこと、元のテンソルの生成元微分係数が
符号付きのpositiveMultiplicationと一致することも証明済み。

残る実際の義務は、innerDifferentialの転置をcobarDifferentialの全長の係数式と同定し、
Signs.sigmaによる符号付き反転と全長Leibniz微分の可換性を証明することです。
その後、finiteDualReversalが実際の制限微分とdualMapを結ぶ鎖同型であること、
頂点成分の有限直和とbigradedComponent全体の同定を完成させます。
単一生成元の係数比較や線形同型だけを鎖同型の完成とは扱いません。

## G7: 原始元・一般の基底・本来の主定理 — 未完了

G6を完成させ、実際の双対bar完全性からGinzburgの各内部次数で原始元を構成します。
r=0の端点も処理し、有限支持の有限和へ戻す必要があります。
ginzburgRegular_of_internal_primitivesは条件付き還元のままです。
三つの一般の三次元空間の基底選択と接続し、標数0・代数閉体上の本来の主定理を宣言・証明します。
