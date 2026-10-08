# 固定環境とコンパイル時のAPI確認 — v3

Lean 4.19.0（commit 6caaee842e94）、mathlib
c44e0c8ee63ca166450922a373c7409c5d26b00b を実際に取得し、全モジュールをビルドした。
依存パッケージの固定値は lake-manifest.json にある。

初版の主な修正は、Submoduleのfinrankへの明示的な書換え、線形写像のextの対象指定、
Module.finrank_pos_iff_exists_ne_zeroによる核の非自明性、次数・符号のcastの扱い、
商のmkQでのsimp only、および有界長の語のFintypeへの型注釈である。
目標定理の仮定やテンソル正則性の意味を変更していない。

平面中の階数2元の存在には Module.End.exists_eigenvalue を使用した。
任意の平面による積の全射性には
Submodule.exists_dual_map_eq_bot_of_lt_top を使用した。
双対の完全性には LinearMap.range_dualMap_eq_dualAnnihilator_ker と
LinearMap.ker_dualMap_eq_dualAnnihilator_range を使用した。
各内部次数の有限性には List.finite_length_le を使用した。

元の環境では配布物未取得だったが、現在は取得済みである。
一部Work実行環境のPID番号と/procの番号の相違には、
scripts/readlink_compat.c の実行ファイル位置の読み取りだけの補正を使用した。
配布Lean本体・kernel・証明方式は変更していない。通常の環境にはこの補正は不要。

今回の bar 実装では Finsupp.lsum、linearCombination、lmapDomain、mapRange.linearMap を使用。
語長の有限性は List.finite_length_eq、正規化部分は冪等線形射影の像として構成しました。
tensorWords、prependChain では推論が曖昧な箇所で (k := k) を明示しています。
Support.lean の有限場合分けは通常の fin_cases と simp によるカーネル検証です。
