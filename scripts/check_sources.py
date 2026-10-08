#!/usr/bin/env python3
"""Textual source audit, explicitly not Lean elaboration or a kernel audit.

Nested Lean comments, line comments and string literals are blanked, preserving
line numbers. Suspicious proof shortcuts and new axiom declarations are rejected.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    depth = 0
    line_comment = False
    string = False
    escaped = False
    i = 0
    while i < len(text):
        ch = text[i]
        pair = text[i:i + 2]
        if line_comment:
            out.append("\n" if ch == "\n" else " ")
            if ch == "\n":
                line_comment = False
            i += 1
        elif depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif string:
            out.append("\n" if ch == "\n" else " ")
            if ch == '"' and not escaped:
                string = False
            if ch == "\\" and not escaped:
                escaped = True
            else:
                escaped = False
            i += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            line_comment = True
            out.extend("  ")
            i += 2
        elif ch == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    if depth or string:
        raise ValueError("Unterminated block comment or string literal")
    return "".join(out)


def audit() -> dict:
    files: list[dict] = []
    declarations: list[dict] = []
    flags: list[dict] = []
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b")
    decl = re.compile(r"\b(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s(:{]+)")
    for path in sorted(ROOT.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        text = path.read_text()
        clean = strip_comments_and_strings(text)
        relative = str(path.relative_to(ROOT))
        for match in forbidden.finditer(clean):
            flags.append({"file": relative, "line": clean.count("\n", 0, match.start()) + 1,
                          "token": match.group(0)})
        for match in decl.finditer(clean):
            declarations.append({"file": relative,
                "line": clean.count("\n", 0, match.start()) + 1,
                "kind": match.group(1), "name": match.group(2)})
        files.append({"file": relative, "lines": len(text.splitlines()),
                      "sha256": hashlib.sha256(text.encode()).hexdigest()})
    counts: dict[str, int] = {}
    for d in declarations:
        counts[d["kind"]] = counts.get(d["kind"], 0) + 1
    report = {
        "audit_kind": "textual, comments and strings removed",
        "lean_executed_by_this_audit": False,
        "kernel_validation": "Not assessed by this textual audit; see VERIFICATION.json and kernel axiom logs.",
        "main_theorem_declared_textually": any(d["kind"] == "theorem" and d["name"] == "tensorRegular_ginzburgRegular" for d in declarations),
        "main_theorem_proof": "Not assessed by this textual audit; see the actual Lean and kernel audit logs.",
        "source_file_count": len(files), "source_line_count": sum(f["lines"] for f in files),
        "declaration_counts": counts, "forbidden_tokens": flags,
        "passed_textual_audit": not flags, "files": files, "declarations": declarations}
    log = ROOT / "logs" / "source_audit.json"
    log.parent.mkdir(exist_ok=True)
    log.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("files", "declarations")},
                     ensure_ascii=False, indent=2))
    return report


if __name__ == "__main__":
    # Regression test for nested comments and strings in the textual scanner.
    example = '/- sorry /- axiom -/ admit -/\n#check "unsafe" -- native_decide\ntheorem ok : True := by trivial'
    assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b",
                         strip_comments_and_strings(example))
    sys.exit(0 if audit()["passed_textual_audit"] else 1)
