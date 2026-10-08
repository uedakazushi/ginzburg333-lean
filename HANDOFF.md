# 引き継ぎ — v4・Aの内部次数付き正規化barから収縮へ

本来の主定理は未宣言・未証明です。TensorRegularとGinzburgRegularの意味は維持。
Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b。
今回の環境 `/workspace/ginzburg333-lean` で scripts/verify.sh 終了0。
34モジュール、明示的theorem308件、全公理監査630件。詳細はVERIFICATION.json。

## 次の入口

Aは完了しました。`Bar/Internal.lean` の internallyNormalizedTerm D i U r n が実際の B_(r,n) です。
内部次数は d.val+wordWeight gs、係数には元の quotientProjection を使います。
internallyNormalizedDifferentialはambientDifferentialの実際の制限で、二乗零と内部次数保存があります。
`Bar/InternalDifferential.lean` の internalProjection_differential は次数射影と微分の可換性、
internallyNormalizedTerm_eq_bot はn<rの零です。
`Bar/InternalExact.lean` の filtration_internal_short_exact は
B_(r,n)(colon)→B_(r,n+1)(smaller)→B_(r,n+1)(U) の実際の短完全列。
internalInclusion_differential と internalQuotient_differential で微分の両立があります。

次はBの自由行正規化bar収縮です。正次数部分 m_+ を先頭因子へ移す
h(m|a_1|…)=−e_i|m_+|a_1|… を実装し、頂点条件と bh+hb を検証してください。
その後はr=0の正内部次数消滅、実際の複体へのquotient_exact_of_exactの適用、
filtration_induction、全空間商とe_i Sの同定によるCの対角外消滅。
続いてDの各nでの有限次元双対とGinzburg道複体の鎖同型、Eの有限支持・一般の基底・主定理。

## APIと実行

internallyNormalizedTermはnormalizedTermとinternalComponentの共通部分。
internalComponentは、d.val+wordWeight gs≠nでの係数射影が零という線形条件です。
internalProjectionはその次数への実際の有限和射影で、正規化・語長条件を保ちます。
内部次数シフトの最高係数次数には inclusion_top_degree を使います。
Homology.ExactAtで型推論が止まる場合はA,B,Cを明示してください。
row型を使う線形写像のextは、`apply LinearMap.ext; intro r` で不要な積分解を避けられます。
型推論が曖昧な場合は `(k := k)` を指定します。

現在のPATHにLeanが無い場合、既存の今回の処理系は
`/workspace/.cloud-tooling/ginzburg333/lean-4.19.0-linux/bin` にあります。
このパスが次回も存在するとは仮定せず、lean --version、mathlib HEAD、Gitの状態を再確認してください。
verify.shは実行ビットが無いので今回は `bash scripts/verify.sh` として実行しました。
変更後はscripts/check_sources.pyとscripts/verify.shを実行し、記録を今回の結果で更新。
main_theorem_proved=falseを維持し、条件付き還元と主定理を区別してください。
