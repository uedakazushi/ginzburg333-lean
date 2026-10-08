#!/usr/bin/env python3
"""Build the Japanese leanblueprint, source links, and a static dependency graph."""
from __future__ import annotations

import hashlib
import html
import json
import os
import pathlib
import re
import shutil
import subprocess
from importlib.metadata import version

ROOT = pathlib.Path(__file__).resolve().parents[1]
BP = ROOT / "blueprint"
SOURCE_COMMIT = (BP / "source_commit.txt").read_text().strip()
REPOSITORY = "https://github.com/uedakazushi/ginzburg333-lean"
ENVIRONMENT = re.compile(
    r"\\begin\{(definition|lemma|theorem|corollary)\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}",
    re.S,
)
NAME = re.compile(r"Ginzburg333(?:\.[A-Za-z_][A-Za-z_0-9]*)+")


def comma_list(text: str) -> list[str]:
    return [x.strip() for x in text.split(",") if x.strip()]


def read_nodes(content: str) -> list[dict]:
    matches = list(ENVIRONMENT.finditer(content))
    nodes = []
    for i, match in enumerate(matches):
        kind, title, body = match.groups()
        labels = re.findall(r"\\label\{([^}]+)\}", body)
        assert len(labels) == 1, (kind, title, labels)
        names = [n for group in re.findall(r"\\lean\{([^}]+)\}", body) for n in comma_list(group)]
        assert names and all(NAME.fullmatch(n) for n in names), labels[0]
        assert r"\leanok" in body, labels[0]
        tail = content[match.end():matches[i + 1].start() if i + 1 < len(matches) else len(content)]
        proof = re.search(r"\\begin\{proof\}(.*?)\\end\{proof\}", tail, re.S)
        if kind != "definition":
            assert proof and r"\leanok" in proof.group(1), labels[0]
        dependencies = [
            label for group in re.findall(r"\\uses\{([^}]+)\}", body + (proof.group(1) if proof else ""))
            for label in comma_list(group)
        ]
        nodes.append({"label": labels[0], "title": title, "kind": kind,
                      "lean": names, "uses": sorted(set(dependencies))})
    by_label = {n["label"]: n for n in nodes}
    assert len(by_label) == len(nodes), "Duplicate labels"
    active, done = set(), set()

    def visit(label):
        assert label in by_label, f"Unknown dependency {label}"
        assert label not in active, f"Cyclic dependency {label}"
        if label in done:
            return
        active.add(label)
        for parent in by_label[label]["uses"]:
            visit(parent)
        active.remove(label)
        done.add(label)

    for label in by_label:
        visit(label)
    return nodes


def declaration_links(nodes: list[dict]) -> dict:
    inventory = json.loads((ROOT / "logs/source_audit.json").read_text())
    assert inventory["passed_textual_audit"]
    for item in inventory["files"]:
        actual = (ROOT / item["file"]).read_bytes()
        assert hashlib.sha256(actual).hexdigest() == item["sha256"], item["file"]
        original = subprocess.check_output(["git", "show", f"{SOURCE_COMMIT}:{item['file']}"], cwd=ROOT)
        assert original == actual, f"Source links must be repinned: {item['file']} changed"
    links = {}
    for name in sorted({name for n in nodes for name in n["lean"]}):
        prefix = name.split(".")[1]
        if prefix == "Comparison":
            directories = ("Ginzburg333/Comparison/", "Ginzburg333/Converse/Main.lean")
        elif prefix in ("Bar", "Converse"):
            directories = (f"Ginzburg333/{prefix}/",)
        elif prefix == "Ginzburg":
            directories = ("Ginzburg333/Ginzburg/", "Ginzburg333/Ginzburg.lean", "Ginzburg333/Converse/")
        else:
            directories = ("Ginzburg333/Finite/", "Ginzburg333/Auxiliary.lean", "Ginzburg333/Signs.lean",
                           "Ginzburg333/Comparison/Primitives.lean", "Ginzburg333/Converse/Main.lean")
        candidates = [d for d in inventory["declarations"]
                      if name.endswith("." + d["name"]) and d["file"].startswith(directories)]
        assert len(candidates) == 1, (name, candidates)
        d = candidates[0]
        links[name] = {"file": d["file"], "line": d["line"], "kind": d["kind"],
                       "url": f"{REPOSITORY}/blob/{SOURCE_COMMIT}/{d['file']}#L{d['line']}"}
    return links


def tex_links(content: str, declarations: dict) -> str:
    def replace(match):
        links = []
        for name in comma_list(match.group(1)):
            label = name.rsplit(".", 1)[-1].replace("_", r"\_")
            links.append(r"\href{" + declarations[name]["url"] + r"}{\texttt{" + label + "}}")
        return match.group(0) + r"\par\noindent\textbf{Lean: }" + r"\par\noindent ".join(links) + r"\par"
    return re.sub(r"\\lean\{([^}]+)\}", replace, content)


def source_finder(declarations: dict):
    directory = BP / "web/find"
    directory.mkdir(parents=True, exist_ok=True)
    data = json.dumps({n: d["url"] for n, d in declarations.items()}, ensure_ascii=False).replace("<", r"\u003c")
    entries = "\n".join(f'<li><a href="{html.escape(d["url"], quote=True)}">{html.escape(n)}</a></li>'
                        for n, d in declarations.items())
    document = f"""<!doctype html>
<html lang="ja"><meta charset="utf-8"><meta name="viewport" content="width=device-width">
<title>Lean宣言とソースの対応</title>
<style>body{{max-width:1000px;margin:3rem auto;padding:0 1rem;font-family:system-ui;line-height:1.8}}a{{overflow-wrap:anywhere}}</style>
<h1>Lean宣言と検証済みソース</h1>
<p>両方向の証明を完成した保存点の、宣言がある行に移動します。</p>
<p id="status" role="status"></p><ul>{entries}</ul>
<script>
const declarations = {data};
const name = decodeURIComponent(location.hash.replace(/^#doc\\//, ""));
if (Object.hasOwn(declarations, name)) location.replace(declarations[name]);
else if (name) document.getElementById("status").textContent = "対応する宣言がありません: " + name;
</script></html>
"""
    (directory / "index.html").write_text(document)


def finish_web(nodes: list[dict], declarations: dict, env: dict):
    macros = {}
    for line in (BP / "src/macros/common.tex").read_text().splitlines():
        match = re.fullmatch(r"\\newcommand\{\\([A-Za-z]+)\}(?:\[(\d+)\])?\{(.*)\}", line)
        if match:
            name, arity, value = match.groups()
            macros[name] = [value, int(arity)] if arity else value
    mathjax = "<script>MathJax = " + json.dumps({"tex": {"macros": macros,
        "inlineMath": [["$", "$"], [r"\(", r"\)"]]}, "options": {"enableMenu": False}}) + ";</script>"
    translations = {"Dependency graph": "依存グラフ", "Home": "本文", "Legend": "凡例",
                    "Contents": "目次", "Uses": "依存する項目", "Proof": "証明",
                    "Boxes": "四角", "Ellipses": "楕円", "definitions": "定義",
                    "theorems and lemmas": "定理と補題", "LaTeX": "本文"}
    targets = {}
    for path in sorted((BP / "web").glob("*.html")):
        document = path.read_text()
        document, replaced = re.subn(r"<script>\s*MathJax\s*=.*?</script>", lambda _: mathjax, document,
                                    count=1, flags=re.S)
        if not replaced:
            document = document.replace('<script type="text/javascript" src="js/mathjax/',
                                        mathjax + '\n<script type="text/javascript" src="js/mathjax/', 1)
        document = document.replace("<html>", '<html lang="ja">').replace('lang="en"', 'lang="ja"')
        for old, new in translations.items():
            document = re.sub(r">(\s*)" + re.escape(old) + r"(\s*)<",
                              lambda m: ">" + m[1] + new + m[2] + "<", document)
        document = "\n".join(line.rstrip() for line in document.splitlines()).rstrip() + "\n"
        path.write_text(document)
        if not path.name.startswith("dep_graph"):
            for n in nodes:
                if f'id="{n["label"]}"' in document:
                    assert n["label"] not in targets, n["label"]
                    targets[n["label"]] = f"web/{path.name}#{n['label']}"
    assert len(targets) == len(nodes), (len(targets), len(nodes), set(n["label"] for n in nodes) - targets.keys())
    source_finder(declarations)
    for path in (BP / "web/styles").glob("*.css"):
        path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()).rstrip() + "\n")
    path = BP / "web/js/plastex.js"
    path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()).rstrip() + "\n")
    dot = ['digraph blueprint {', 'graph [rankdir=TB,bgcolor="white",nodesep=0.35,ranksep=0.65];',
           'node [fontname="Noto Sans CJK JP",fontsize=11,style="filled",fillcolor="#d9f2e3"];',
           'edge [color="#607d8b"];']
    for i, n in enumerate(nodes, 1):
        attributes = {"label": f'{i}. {n["title"]}', "URL": targets[n["label"]],
                      "target": "_top", "tooltip": n["label"],
                      "shape": "box" if n["kind"] == "definition" else "ellipse"}
        attrs = ",".join(k + "=" + json.dumps(v, ensure_ascii=False) for k, v in attributes.items())
        dot.append(json.dumps(n["label"]) + " [" + attrs + "];")
        for parent in n["uses"]:
            dot.append(json.dumps(parent) + " -> " + json.dumps(n["label"]) + ";")
    dot.append("}")
    (BP / "dependency_graph.dot").write_text("\n".join(dot) + "\n")
    subprocess.run(["dot", "-Tsvg", str(BP / "dependency_graph.dot"), "-o", str(BP / "dependency_graph.svg")], check=True, env=env)


def main():
    content = (BP / "src/content.tex").read_text()
    nodes = read_nodes(content)
    declarations = declaration_links(nodes)
    manifest = {"language": "ja", "source_commit": SOURCE_COMMIT, "repository": REPOSITORY,
                "graph_kind": "curated mathematical dependencies, not all Lean proof-term dependencies",
                "nodes": nodes, "declarations": declarations}
    (BP / "declarations.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
    (BP / "src/linked_content.tex").write_text(tex_links(content, declarations))
    env = os.environ.copy()
    for variable, folder in (("XDG_CACHE_HOME", "cache"), ("TEXMFVAR", "texmf-var"), ("TEXMFCONFIG", "texmf-config")):
        p = ROOT / ".tooling/blueprint" / folder
        p.mkdir(parents=True, exist_ok=True)
        env[variable] = str(p)
    assert version("leanblueprint") == "0.0.20"
    for command in ("pdf", "web"):
        log_path = ROOT / f"logs/blueprint_{command}.log"
        with log_path.open("w") as log:
            subprocess.run(["leanblueprint", command], cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        log_path.write_text(log_path.read_text().rstrip() + "\n")
    generated = {x.strip() for x in (BP / "lean_decls").read_text().splitlines() if x.strip()}
    assert generated == set(declarations), (generated ^ set(declarations))
    (BP / "lean_decls").write_text("\n".join(sorted(generated)) + "\n")
    finish_web(nodes, declarations, env)
    shutil.copyfile(BP / "print/print.pdf", BP / "web/blueprint_ja.pdf")
    (BP / "web/.nojekyll").write_text("")
    print(json.dumps({"nodes": len(nodes), "Lean_declarations": len(declarations),
                      "html_pages": len(list((BP / "web").rglob("*.html"))),
                      "pdf_bytes": (BP / "print/print.pdf").stat().st_size}, ensure_ascii=False))


if __name__ == "__main__":
    main()
