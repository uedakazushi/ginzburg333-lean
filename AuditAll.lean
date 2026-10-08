import Ginzburg333
import Lean.Util.CollectAxioms

/- Every theorem in the project namespace, including generated theorems,
   is checked against the standard-axiom allowlist. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants do
    if (`Ginzburg333).isPrefixOf name then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in theorem {name}"
    logInfo m!"AUDIT {name}: {axioms}"
  logInfo m!"PROJECT_THEOREMS_CHECKED: {names.size}"
