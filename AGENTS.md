# Agent instructions for this local Lean project

The target is the avatar-free implication from tensor regularity to Ginzburg
regularity for the labelled (3,3,3) quiver over an algebraically closed field
of characteristic zero. Inputs are in docs/.

The v3 source snapshot builds with Lean 4.19.0 and the pinned mathlib commit.
All source theorem declarations compile. AuditAll.lean audits all theorems in
namespace Ginzburg333 against propext, Classical.choice and Quot.sound.
The main theorem is still absent. Normalized bar terms, their square-zero
differential, internal grading, shifted short exact sequences, actual normalized
free-row contraction, and off-diagonal filtration vanishing are implemented.
Finite internal-degree duals and signed reversal are vector-space equivalences;
the full bar/Ginzburg chain isomorphism is NOT implemented.
Do not describe predicate induction as the completed bar-complex argument.

Never add sorry/admit, fresh axioms, unsafe proof mechanisms, or a hypothesis
that contains the intended conclusion. Do not weaken TensorRegular or redefine
GinzburgRegular to mean a certificate. Preserve finite support and vertex/path
conventions. Keep the three k^3 factors conceptually distinct.

After changing Lean sources run scripts/check_sources.py, then scripts/verify.sh.
Record exit codes, the current source inventory, build output and axiom output.
Python tests are independent checks, not Lean verification. Update STATUS.md,
GAPS.md, HANDOFF.md and VERIFICATION.json truthfully. Preserve
main_theorem_proved=false until the actual theorem is proved.

The user authorized publishing verified checkpoints to the current origin,
uedakazushi/ginzburg333-lean, on main. Do not claim a push, CI run, asynchronous
job or publication that has not occurred. No license has been added. Linux tooling can be
bootstrapped with scripts/bootstrap.sh. The readlink compatibility shim fixes
only executable path discovery in PID namespaces and does not change Lean's
kernel or proof validation.
