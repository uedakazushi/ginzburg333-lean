# Agent instructions for this local Lean project

The target is the avatar-free implication from tensor regularity to Ginzburg
regularity for the labelled (3,3,3) quiver over an algebraically closed field
of characteristic zero. Inputs are in docs/.

The v3 source snapshot builds with Lean 4.19.0 and the pinned mathlib commit.
All source theorem declarations compile. AuditAll.lean audits all theorems in
namespace Ginzburg333 against propext, Classical.choice and Quot.sound.
The avatar-free main theorem is implemented in Comparison/Primitives.lean:
Ginzburg333.tensorRegular_ginzburgRegular. Actual normalized bar grading,
shifted short exact sequences, normalized free-row contraction, filtration
vanishing, finite-degree dual/path chain isomorphisms and finite-support
primitives are implemented. Comparison/Bases.lean connects independent
three-dimensional factors through their genuine tensor-product basis.
Do not describe predicate induction as the completed bar-complex argument.

Never add sorry/admit, fresh axioms, unsafe proof mechanisms, or a hypothesis
that contains the intended conclusion. Do not weaken TensorRegular or redefine
GinzburgRegular to mean a certificate. Preserve finite support and vertex/path
conventions. Keep the three k^3 factors conceptually distinct.

After changing Lean sources run scripts/check_sources.py, then scripts/verify.sh.
Record exit codes, the current source inventory, build output and axiom output.
Python tests are independent checks, not Lean verification. Update STATUS.md,
GAPS.md, HANDOFF.md and VERIFICATION.json truthfully. Preserve
main_theorem_proved=true only while the actual theorem and required kernel checks pass.

The user authorized publishing verified checkpoints to the current origin,
uedakazushi/ginzburg333-lean, on main. Do not claim a push, CI run, asynchronous
job or publication that has not occurred. No license has been added. Linux tooling can be
bootstrapped with scripts/bootstrap.sh. The readlink compatibility shim fixes
only executable path discovery in PID namespaces and does not change Lean's
kernel or proof validation.

Current additional goal: prove GinzburgRegular -> TensorRegular and equivalence.
Converse/LowDegree excludes rank zero; Euler/Paths/Counting prove actual
finite-degree Jacobi growth. The rank-one free-corner lower bound and converse
main theorem remain unfinished. Preserve the proved forward theorem.
