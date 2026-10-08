#!/usr/bin/env bash
# Fail closed: no successful verification status without a real Lean invocation.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p logs
python3 scripts/check_sources.py | tee logs/source_audit.txt
{
  printf 'Verification attempted at UTC: '
  date -u +%Y-%m-%dT%H:%M:%SZ
  printf 'Target toolchain: '
  cat lean-toolchain
  printf 'lean path: '
  command -v lean || true
  printf 'lake path: '
  command -v lake || true
} | tee logs/environment.txt
if ! command -v lean >/dev/null 2>&1 || ! command -v lake >/dev/null 2>&1; then
  echo 'BLOCKED: Lean/lake not installed. No elaboration, kernel audit or lake build has run.' | tee logs/build_status.txt
  exit 127
fi
# `lean-toolchain` selects the pinned toolchain when elan is installed.
lake env lean --version | tee logs/lean_version.txt
if ! grep -q 'version 4.19.0' logs/lean_version.txt; then
  echo 'BLOCKED: Unexpected Lean version. Restore the pinned toolchain first.' | tee logs/build_status.txt
  exit 2
fi
if ! lake build 2>&1 | tee logs/lake_build.log; then
  echo 'FAILED: lake build did not succeed.' | tee logs/build_status.txt
  exit 1
fi
if ! lake env lean Audit.lean 2>&1 | tee logs/kernel_axioms.log; then
  echo 'FAILED: Audit.lean did not succeed.' | tee logs/build_status.txt
  exit 1
fi
if ! lake env lean AuditAll.lean 2>&1 | tee logs/kernel_axioms_all.log; then
  echo 'FAILED: Full project axiom audit did not succeed.' | tee logs/build_status.txt
  exit 1
fi
if grep -E 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler' logs/kernel_axioms.log logs/kernel_axioms_all.log; then
  echo 'FAILED: Found an unacceptable proof dependency.' | tee logs/build_status.txt
  exit 1
fi
# AuditAll checks every theorem in the project namespace against the allowlist.
echo 'LIBRARY BUILT; all project theorem axioms are standard. The main theorem is still absent.' | tee logs/build_status.txt
