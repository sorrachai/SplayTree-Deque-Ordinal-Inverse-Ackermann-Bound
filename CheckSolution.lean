module

import Solution
import Lean.Util.CollectAxioms

/-! Audit the dependency closure of the completed solution, independently of
the reference challenge's intentional proof hole. -/

open Lean Elab Command in
run_elab do
  let forbidden : Array Name := #[`Solution.LegacyDefinitions, `Solution.LegacyProof, `Solution.Bridge]
  let imported := (← getEnv).allImportedModuleNames
  let legacyImports := imported.filter fun name => forbidden.any (·.isPrefixOf name)
  unless legacyImports.isEmpty do
    throwError "The direct solution imports legacy proof/conversion modules: {legacyImports}"
  logInfo "The solution imports no legacy proof or conversion modules."
  let name := ``deque_ordinal_omega_ackermann_bound
  let axioms ← collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom in {name}: {axiomName}"
  logInfo m!"{name} uses only standard Lean axioms: {axioms}"

#check Solution.deque_ordinal_omega_explicit_bound
