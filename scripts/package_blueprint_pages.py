#!/usr/bin/env python3
"""Package checked blueprint artifacts for a GitHub Pages project site."""
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import shutil
import subprocess
from urllib.parse import unquote, urlsplit

from check_blueprint import Links
from build_blueprint import BP, ROOT, SOURCE_COMMIT


def main():
    record = json.loads((BP / "verification.json").read_text())
    assert record["status"] == "BLUEPRINT_BUILT_AND_CHECKED"
    assert record["mathematical_source_commit"] == SOURCE_COMMIT
    assert record["lean_declaration_check_exit_code"] == 0
    for name, digest in record["artifacts"].items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name

    site = ROOT / ".tooling/pages"
    assert site.resolve().is_relative_to((ROOT / ".tooling").resolve())
    if site.exists():
        shutil.rmtree(site)
    shutil.copytree(BP / "web", site)
    for name in ("verification.json", "declarations.json"):
        shutil.copyfile(BP / name, site / name)
    index = site / "index.html"
    document = index.read_text()
    assert "</h1>" in document
    navigation = ('\n<p><a href="blueprint_ja.pdf">日本語PDFを読む</a> · '
                  '<a href="dep_graph_document.html">証明の依存グラフ</a> · '
                  '<a href="https://github.com/uedakazushi/ginzburg333-lean">Leanソース</a></p>')
    index.write_text(document.replace("</h1>", "</h1>" + navigation, 1))

    pages = {}
    for path in site.rglob("*.html"):
        parser = Links()
        parser.feed(path.read_text())
        pages[path.resolve()] = parser
    names = set(json.loads((site / "declarations.json").read_text())["declarations"])
    checked = 0
    for path, parser in pages.items():
        for reference in parser.references:
            url = urlsplit(reference)
            if url.scheme or url.netloc:
                continue
            assert not url.path.startswith("/"), (path, reference)
            target = (path.parent / unquote(url.path)).resolve() if url.path else path
            assert target.is_relative_to(site.resolve()), (path, reference)
            if target.is_dir():
                target = target / "index.html"
            assert target.is_file(), (path, reference)
            if url.fragment and target in pages:
                if target == (site / "find/index.html").resolve():
                    assert unquote(url.fragment).removeprefix("doc/") in names, reference
                else:
                    assert unquote(url.fragment) in pages[target].ids, (path, reference)
            checked += 1
    assert (site / ".nojekyll").is_file()
    assert (site / "blueprint_ja.pdf").read_bytes() == (BP / "print/print.pdf").read_bytes()
    revision = os.environ.get("GITHUB_SHA") or subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    provenance = {"revision": revision, "mathematical_source_commit": SOURCE_COMMIT,
                  "blueprint_verification": "verification.json", "html_pages": len(pages),
                  "local_references_checked": checked,
                  "project_site_relative_urls_checked": True,
                  "pdf_sha256": hashlib.sha256((site / "blueprint_ja.pdf").read_bytes()).hexdigest()}
    (site / "site-build.json").write_text(json.dumps(provenance, ensure_ascii=False, indent=2) + "\n")
    (ROOT / "logs/pages_package.json").write_text(json.dumps(provenance, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(provenance, ensure_ascii=False))


if __name__ == "__main__":
    main()
