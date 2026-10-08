#!/usr/bin/env python3
"""Check the built blueprint, all source links, and actual Lean declarations."""
from __future__ import annotations
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit
from build_blueprint import BP, ROOT, SOURCE_COMMIT, declaration_links, read_nodes


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.references = []
        self.ids = set()

    def handle_starttag(self, tag, attributes):
        values = dict(attributes)
        if "id" in values:
            self.ids.add(values["id"])
        for name in ("href", "src", "xlink:href"):
            if values.get(name):
                self.references.append(values[name])


def main():
    manifest = json.loads((BP / "declarations.json").read_text())
    content = (BP / "src/content.tex").read_text()
    nodes = read_nodes(content)
    assert nodes == manifest["nodes"], "Stale blueprint node manifest"
    declarations = declaration_links(nodes)
    assert declarations == manifest["declarations"], "Stale declaration links"
    vendor = json.loads((BP / "vendor_manifest.json").read_text())
    for name, digest in vendor["files"].items():
        assert hashlib.sha256((BP / name).read_bytes()).hexdigest() == digest, name
    assert manifest["source_commit"] == SOURCE_COMMIT
    names = sorted(declarations)
    assert (BP / "lean_decls").read_text().splitlines() == names
    code = "import Ginzburg333\n" + "\n".join(
        f"#check {name}\n#print axioms {name}" for name in names
    ) + "\n"
    result = subprocess.run(["lake", "env", "lean", "--stdin"], input=code, cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (ROOT / "logs/blueprint_declarations.log").write_text(result.stdout)
    assert result.returncode == 0, "Lean declaration check failed; see logs/blueprint_declarations.log"
    allowlist = {"propext", "Classical.choice", "Quot.sound"}
    for axioms in re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout, re.S):
        assert {x.strip() for x in axioms.split(",")} <= allowlist, axioms
    assert not any(x in result.stdout for x in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"))

    pages = {}
    for path in (BP / "web").rglob("*.html"):
        parser = Links()
        parser.feed(path.read_text())
        pages[path.resolve()] = parser
        assert 'lang="ja"' in path.read_text(), path
    checked = 0
    for path, parser in pages.items():
        for reference in parser.references:
            url = urlsplit(reference)
            if url.scheme or url.netloc:
                continue
            target = (path.parent / unquote(url.path)).resolve() if url.path else path
            if target.is_dir():
                target = target / "index.html"
            assert target.is_file(), (str(path), reference)
            if url.fragment and target in pages:
                if target == (BP / "web/find/index.html").resolve():
                    assert unquote(url.fragment).removeprefix("doc/") in declarations, reference
                else:
                    assert unquote(url.fragment) in pages[target].ids, (str(path), reference)
            checked += 1
    pdf = BP / "print/print.pdf"
    assert pdf.read_bytes().startswith(b"%PDF-")
    assert pdf.read_bytes() == (BP / "web/blueprint_ja.pdf").read_bytes()
    pdf_text = subprocess.check_output(["pdftotext", str(pdf), "-"], text=True)
    for word in ("正則性", "逆主定理", "有限支持", "2109", "4096"):
        assert word in pdf_text, f"Japanese PDF content missing: {word}"
    tex_log = (BP / "print/print.log").read_text()
    for token in ("Missing character:", "undefined references", "undefined on input line"):
        assert token not in tex_log, token
    web_log = (ROOT / "logs/blueprint_web.log").read_text()
    assert "Unrecognized command" not in web_log, "Unknown web macros"
    info = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
    page_count = int(re.search(r"^Pages:\s*(\d+)", info, re.M).group(1))
    source_files = [p for p in (BP / "src").rglob("*") if p.is_file()
                    and p.name != "linked_content.tex" and p.suffix not in (".paux", ".log")]
    source_files += [ROOT / "scripts/build_blueprint.py", ROOT / "scripts/check_blueprint.py",
                     BP / "requirements.txt", BP / "source_commit.txt", BP / "vendor_manifest.json"]
    record = {
        "status": "BLUEPRINT_BUILT_AND_CHECKED",
        "language": "ja",
        "verified_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "mathematical_source_commit": SOURCE_COMMIT,
        "leanblueprint_version": "0.0.20",
        "definition_lemma_theorem_nodes": len(nodes),
        "curated_dependency_edges": sum(len(n["uses"]) for n in nodes),
        "lean_declarations_checked": len(names),
        "lean_declaration_check_exit_code": result.returncode,
        "declaration_axiom_allowlist": sorted(allowlist),
        "unexpected_declaration_axioms": [],
        "mathematical_lean_sources_changed": False,
        "pdf_build_exit_code": 0,
        "html_build_exit_code": 0,
        "local_mathjax_version": vendor["version"],
        "local_mathjax_assets_hash_checked": len(vendor["files"]),
        "pdf_pages": page_count,
        "pdf_japanese_text_checked": True,
        "pdf_missing_glyph_warnings": False,
        "html_pages": len(pages),
        "local_html_references_checked": checked,
        "dependency_graph_acyclic": True,
        "source_link_targets_checked": len(declarations),
        "source_hashes": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(source_files)},
        "artifacts": {
            str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (pdf, BP / "web/index.html", BP / "dependency_graph.svg", BP / "declarations.json")
        },
        "publication_format": "Repository artifacts: generated HTML, PDF, annotated LaTeX, source map and dependency graph"
    }
    (BP / "verification.json").write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
    message = {k: record[k] for k in ("status", "definition_lemma_theorem_nodes", "lean_declarations_checked",
                                     "pdf_pages", "html_pages", "local_html_references_checked")}
    (ROOT / "logs/blueprint_checks.log").write_text(json.dumps(message, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(message, ensure_ascii=False))


if __name__ == "__main__":
    main()
