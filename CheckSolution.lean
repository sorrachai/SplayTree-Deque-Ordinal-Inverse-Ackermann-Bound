module

import Challenge
import Lean.Util.CollectAxioms

/-! Audit the dependency closure of the public challenge theorem. -/

open Lean Elab Command in
run_elab do
  let name := ``deque_ordinal_omega_ackermann_bound
  let axioms ← collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom in {name}: {axiomName}"
  logInfo m!"{name} uses only standard Lean axioms: {axioms}"

#check Solution.deque_ordinal_omega_explicit_bound
