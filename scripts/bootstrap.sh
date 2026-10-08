#!/usr/bin/env bash
# A local Linux toolchain fallback. Normal elan installations use the pinned toolchain.
set -euo pipefail
cd "$(dirname "$0")/.."
project_root="$(pwd)"
if [ "$#" -eq 0 ]; then set -- ./scripts/verify.sh; fi
if command -v lean >/dev/null 2>&1 && command -v lake >/dev/null 2>&1 && lean --version 2>/dev/null | grep -q 'version 4.19.0'; then
  exec "$@"
fi
if [ "$(uname -s)" != Linux ]; then
  echo 'Install elan for your platform, then run ./scripts/verify.sh.' >&2
  exit 127
fi
task_tooling="${GINZBURG333_TOOLING:-$project_root/.tooling}"
task_lean="$task_tooling/lean-4.19.0-linux"
mkdir -p "$task_tooling"
if [ ! -x "$task_lean/bin/lean" ]; then
  task_archive="$task_tooling/lean-4.19.0-linux.tar.zst"
  curl -fL --retry 3 --connect-timeout 20 \
    https://github.com/leanprover/lean4/releases/download/v4.19.0/lean-4.19.0-linux.tar.zst \
    -o "$task_archive"
  tar --no-same-owner --zstd -xf "$task_archive" -C "$task_tooling"
fi
export PATH="$task_lean/bin:$PATH"
if ! lean --version >"$task_tooling/lean_version.txt" 2>"$task_tooling/lean_error.txt"; then
  if ! grep -q 'failed to locate application' "$task_tooling/lean_error.txt"; then
    cat "$task_tooling/lean_error.txt" >&2
    exit 1
  fi
  cc -shared -fPIC scripts/readlink_compat.c -o "$task_tooling/readlink_compat.so" -ldl
  export LD_PRELOAD="$task_tooling/readlink_compat.so${LD_PRELOAD:+:$LD_PRELOAD}"
fi
lean --version
if [ ! -f lake-manifest.json ]; then lake update; fi
lake exe cache get \
  Mathlib.LinearAlgebra.Eigenspace.Triangularizable Mathlib.LinearAlgebra.Dual.Lemmas \
  Mathlib.LinearAlgebra.Finsupp.LinearCombination Mathlib.Data.Fin.VecNotation \
  Mathlib.Tactic.FinCases Mathlib.Tactic.Ring Mathlib.Tactic.NormNum Mathlib.Tactic.Push \
  Mathlib.LinearAlgebra.Quotient.Basic Mathlib.Data.Nat.Choose.Basic \
  Mathlib.Algebra.BigOperators.Group.List.Basic Mathlib.Data.Set.Finite.List \
  Mathlib.Tactic.DeriveFintype Mathlib.Data.Fintype.Prod Mathlib.Data.Finite.Prod \
  Mathlib.Data.Matrix.Basis Mathlib.Algebra.MonoidAlgebra.Basic \
  Mathlib.LinearAlgebra.TensorProduct.RightExactness Mathlib.LinearAlgebra.TensorProduct.Basis \
  Mathlib.Algebra.Ring.Commute Mathlib.LinearAlgebra.Dual.Basis \
  Mathlib.LinearAlgebra.Finsupp.VectorSpace Mathlib.LinearAlgebra.Pi \
  Mathlib.LinearAlgebra.Finsupp.Defs
exec "$@"
