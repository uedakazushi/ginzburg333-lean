# 数学的義務の完了状況 — v4

**要求されたA〜Eと本来の主定理は証明済みです。残る形式化の穴はありません。**
`bash scripts/verify.sh`終了0、明示的theorem 433件、全公理監査923件。
追加公理、sorry、admit、結論を含む仮定はありません。

## G1–G3 / A: 補助代数・商加群・内部次数付きbar

元の24次元補助代数、21正次数基底、商作用、colonとfiltrationを維持。
頂点と係数の最初の頂点射影を課した実際の正規化barに内部次数を実装しました。
射影と微分の可換性、有限次元性、包含次数+1付き短完全列と鎖写像を証明済み。

## G4 / B〜C: 正規化自由収縮とfiltration

rowContraction_homotopy_normalizedは実際のnormalizedTermでBH+HB=1を証明します。
零部分空間商の内部次数別完全性、r=0,n>0の消滅、n<rの零を基底に、
実際の短完全列を使った帰納法でnormalized_bar_off_diagonalを証明しました。
全空間商と頂点単純加群も同定済み。内部次数0のTor_0の消滅は仮定していません。

## G5–G6 / D: 実際のGinzburg微分と有限双対の鎖同型

各内部次数の有限bar双対を使い、全barの無限直積双対を用いません。
生成元の構造定数、innerDifferentialとcobarDifferentialの全長の転置式、
Signs.sigmaによる因子反転とLeibniz微分の全長の可換性を証明しました。
finiteDualReversal_differentialは頂点別の実際の制限微分とdualMapの両立です。
totalDualReversalとtotalDualReversal_differentialは三頂点を合わせた
有限双対と実際のbigradedComponent全体の鎖同型を与えます。

## G7 / E: 原始元、基底選択、主定理

rowPath_primitive、ginzburg_internal_primitivesが実際の有限支持原始元を構成します。
負次数では非零支持語は空語にならないことも証明し、端点を処理しました。
既存の内部次数の有限和還元に適用し、tensorRegular_ginzburgRegularを証明済み。
既存の条件付き還元補題と完成した主定理は別の宣言です。

Bases.leanのtensorCoordinatesEquivは、独立した三つの空間X、Y、Zの
実際のテンソル積基底の座標同型です。chosenTensorCoordinatesは各finrank=3から
独立に基底を選び、元の両述語の含意へ接続します。
これは選んだ座標での定理であり、別途の基底非依存dgモデルの定義や
GL作用に関する追加定理を主張するものではありません。
