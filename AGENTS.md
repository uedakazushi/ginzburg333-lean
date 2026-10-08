# Agent instructions for this local Lean project

The target is the avatar-free equivalence of tensor regularity and Ginzburg
regularity for the labelled (3,3,3) quiver over an algebraically closed field
of characteristic zero. Both implications are proved; the converse holds over
any field. Inputs are in docs/.

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

The converse is proved in Converse/Main.lean as
Ginzburg333.ginzburgRegular_tensorRegular, and the equivalence is
Ginzburg333.ginzburgRegular_iff_tensorRegular. Converse/Euler and Counting
derive actual finite-degree Jacobi growth from negative exactness. Factors,
Quotient, Representation, MatrixRelations, WordMap and JacobiMap construct
the genuine free-corner representation; LoopLifts and Growth establish the
exponential lower bound and the converse contradiction. Preserve both original
predicates and both implications. Record converse/equivalence proof status
only after the corresponding theorem and required kernel checks pass.

The Japanese leanblueprint is in blueprint/src/content.tex. Generated HTML and
Japanese PDF are tracked under blueprint/web and blueprint/print/print.pdf.
Use scripts/build_blueprint.py and scripts/check_blueprint.py with the pinned
blueprint/requirements.txt. These preserve the Lean dependency pins and use
actual Lean declaration/axiom checks without adding a checkdecls dependency.
Source links are pinned by blueprint/source_commit.txt; mathematical source
changes require updating the pin and correspondence. Record document build,
declaration checks and browser inspection truthfully in blueprint/verification.json
and VERIFICATION.json. Publishing the repository and blueprint is user-authorized.
