# 生成ツールと同梱資源

本文はこのリポジトリの日本語blueprintです。HTMLのテーマ、依存グラフの実装などは、
以下の固定された生成ツールが提供する資源を使っています。

| ツール | 版 | 保存したライセンス |
|---|---|---|
| leanblueprint | 0.0.20 | [Apache 2.0](licenses/leanblueprint.txt) |
| plasTeX | 3.1 | [MIT](licenses/plasTeX.txt) |
| plastexdepgraph | 0.0.5 | [Apache 2.0](licenses/plastexdepgraph.txt) |
| plastexshowmore | 0.0.2 | [Apache 2.0](licenses/plastexshowmore.txt) |
| MathJax | 3.2.2 | [Apache 2.0](web/js/mathjax/LICENSE) |

生成されたHTMLには各ツールが配布するjQuery、D3、d3-graphviz、
HPCC WebAssemblyなどの資源も含まれます。配布ファイルのヘッダーは保持しています。
MathJaxの配布元と同梱ファイルのハッシュは[vendor_manifest.json](vendor_manifest.json)に記録しています。
PDFの日本語フォントはNoto CJKで、XeLaTeXにより埋め込んでいます。
Pythonの依存バージョンは[requirements.txt](requirements.txt)に固定しています。
