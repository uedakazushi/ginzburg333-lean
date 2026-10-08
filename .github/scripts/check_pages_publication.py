#!/usr/bin/env python3
"""Check the deployed project site over public HTTPS without credentials."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import pathlib
import re
import time
import urllib.request
from urllib.parse import urljoin

ROOT = pathlib.Path(__file__).resolve().parents[2]
SOURCE = (ROOT / "blueprint/source_commit.txt").read_text().strip()


def fetch(url):
    with urllib.request.urlopen(url, timeout=20) as response:
        body = response.read()
        record = {"url": url, "http_status": response.status,
                  "content_type": response.headers.get("Content-Type"),
                  "authentication_sent": False, "bytes": len(body),
                  "sha256": hashlib.sha256(body).hexdigest()}
    assert record["http_status"] == 200, record
    return body, record


def latest_deployment_revision():
    url = ("https://api.github.com/repos/uedakazushi/ginzburg333-lean/actions/workflows/"
           "blueprint-pages.yml/runs?branch=main&status=success&per_page=10")
    body, _ = fetch(url)
    runs = json.loads(body)["workflow_runs"]
    return next(r["head_sha"] for r in runs if r["event"] != "pull_request")


def check(base, revision):
    results = []

    def get(path):
        body, record = fetch(urljoin(base, path))
        results.append(record)
        return body

    provenance = json.loads(get("site-build.json"))
    assert provenance["revision"] == revision, provenance
    assert provenance["mathematical_source_commit"] == SOURCE, provenance
    verification = json.loads(get("verification.json"))
    assert verification["status"] == "BLUEPRINT_BUILT_AND_CHECKED"
    assert verification["mathematical_source_commit"] == SOURCE
    assert verification["lean_declaration_check_exit_code"] == 0
    assert verification["unexpected_declaration_axioms"] == []
    page = get("").decode()
    assert 'lang="ja"' in page and "Ginzburg" in page
    assert 'href="blueprint_ja.pdf"' in page
    graph = get("dep_graph_document.html").decode()
    assert "thm:equivalence" in graph
    finder = get("find/index.html").decode()
    assert SOURCE in finder and "Ginzburg333.ginzburgRegular_iff_tensorRegular" in finder
    pdf = get("blueprint_ja.pdf")
    assert pdf.startswith(b"%PDF-")
    assert hashlib.sha256(pdf).hexdigest() == provenance["pdf_sha256"]
    assert provenance["pdf_sha256"] == verification["artifacts"]["blueprint/print/print.pdf"]
    vendor = json.loads((ROOT / "blueprint/vendor_manifest.json").read_text())["files"]
    for path in ("js/mathjax/tex-chtml-full.js",
                 "js/mathjax/output/chtml/fonts/woff-v2/MathJax_Main-Regular.woff"):
        assert hashlib.sha256(get(path)).hexdigest() == vendor["web/" + path]
    for path in ("js/graphvizlib.wasm", "js/expatlib.wasm"):
        assert get(path).startswith(b"\x00asm")
        assert results[-1]["content_type"].split(";", 1)[0] == "application/wasm"
    return {"status": "PUBLIC_PAGES_HTTP_CHECKS_PASSED", "site_url": base,
            "deployed_revision": revision, "mathematical_source_commit": SOURCE,
            "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "pdf_sha256": provenance["pdf_sha256"], "pdf_pages": verification["pdf_pages"],
            "html_pages": verification["html_pages"], "checks": results,
            "all_http_statuses_200": True, "pdf_and_vendor_hashes_match": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--url", default="https://uedakazushi.github.io/ginzburg333-lean/")
    parser.add_argument("--revision", default="")
    args = parser.parse_args()
    revision = args.revision or latest_deployment_revision()
    assert re.fullmatch(r"[0-9a-f]{40}", revision)
    for attempt in range(10):
        try:
            record = check(args.url.rstrip("/") + "/", revision)
            break
        except Exception:
            if attempt == 9:
                raise
            time.sleep(10)
    output = ROOT / "logs/pages_http.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ("status", "site_url", "deployed_revision",
                                           "pdf_pages", "all_http_statuses_200")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
