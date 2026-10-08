# 日本語 Lean blueprint

標数0の代数閉体上の `Ginzburg.GinzburgRegular w ↔ TensorRegular w` を、
定義・補題・証明の依存関係から読むための日本語blueprintです。
順方向A〜Eと、任意の体上で成立する逆方向の証明を含みます。

- [GitHub PagesのHTML公開先](https://uedakazushi.github.io/ginzburg333-lean/)
- [Pagesの日本語PDF公開先](https://uedakazushi.github.io/ginzburg333-lean/blueprint_ja.pdf)
- [日本語PDF（10ページ）](print/print.pdf)
- [HTML版の入口](web/index.html)：数式、折り畳める証明、操作できる依存グラフ。
- [依存グラフのSVG](dependency_graph.svg)
- [本文のLaTeXソース](src/content.tex)
- [Lean宣言とソース行の対応](declarations.json)
- [blueprintの検証結果](verification.json)

51項目に103件のLean宣言を対応させています。リンクは、両主定理を完成した
保存点 `ea11e52179e60a9a64b673f43538a8a448e23b74` の宣言行を指します。
グラフの118本の辺は本文で選んだ数学的依存関係です。
全ての対応宣言を実際のLeanで検査し、公理依存も確認しています。

HTMLとPDFは生成済みの成果物をリポジトリに同梱しています。
HTMLをローカルで閲覧するには、リポジトリのルートで以下を実行し、
`http://localhost:8000/` を開いてください。

```sh
python3 -m http.server 8000 --directory blueprint/web
```

数式用のMathJaxとフォント、依存グラフ用のJavaScript・WebAssemblyを同梱しているため、
閲覧時に外部CDNから読み込む必要はありません。
ノードをクリックすると日本語の主張とLeanリンクが開きます。

## GitHub ActionsからのPages公開

[blueprint-pages.yml](../.github/workflows/blueprint-pages.yml)は、mainへの関連ファイルのpushで
全Leanソースと公理を検証し、日本語PDF・HTMLを生成、103件の実際のLean宣言とリンクを検査します。
成功した成果物をGitHub Pagesへデプロイします。pull requestでは生成・検査までを実行します。
Actions画面から手動実行もできます。文書生成・Lean検証のログはActionsのartifactに保存されます。
Lean検証・文書生成・デプロイは別jobであり、文書側の失敗時はfailed jobsだけを再実行できます。

初回は所有者がリポジトリのSettings → Pages → Build and deployment → Sourceを
**GitHub Actions**に設定してください。追加のsecretは不要です。
公開状態は[Actions](https://github.com/uedakazushi/ginzburg333-lean/actions/workflows/blueprint-pages.yml)で確認できます。
上記のPages URLはデプロイ成功後に利用できます。

## 再生成と検査

Leanはリポジトリの固定環境を使います。文書生成にはPython 3.12、Graphviz、
XeLaTeX、latexmk、xeCJK、Noto CJKフォント、検査にはpoppler-utilsが必要です。
Debian/Ubuntuでは対応するTeX関連パッケージは
`texlive-xetex texlive-lang-cjk texlive-lang-chinese texlive-fonts-recommended fonts-noto-cjk latexmk graphviz poppler-utils` です。

```sh
python3 -m venv .tooling/blueprint-venv
.tooling/blueprint-venv/bin/pip install -r blueprint/requirements.txt
export PATH="$PWD/.tooling/blueprint-venv/bin:$PATH"
python3 scripts/build_blueprint.py
python3 scripts/check_blueprint.py
bash scripts/verify.sh
```

`build_blueprint.py` は標準のleanblueprint 0.0.20を使い、本文からリンク付き原稿、
PDF、HTML、静的グラフを生成します。対応する数学ソースに変更があれば、
保存点とリンクを更新するまで生成を拒否します。
`check_blueprint.py` は宣言と公理の実際のLean検査、日本語PDFの文字抽出、
HTML内部リンク、依存関係の非循環性、同梱MathJaxのハッシュを検査します。
blueprintの標準CLIが提供する外部checkdecls依存を追加せず、固定されたLean依存を維持しています。

生成ツール・同梱資源の情報は[THIRD_PARTY.md](THIRD_PARTY.md)にあります。
