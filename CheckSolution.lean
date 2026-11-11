module

import Solution
import Lean.Util.CollectAxioms

/-! Audit the dependency closure and kernel axioms of all 30 root theorems in `Solution`,
independently of the reference `Challenge` blueprint. -/

open Lean Elab Command in
run_elab do
  let imported := (← getEnv).allImportedModuleNames
  if imported.contains `Challenge then
    throwError "Solution transitively imports Challenge!"
  let forbidden : Array Name := #[
    `Solution.LegacyDefinitions,
    `Solution.LegacyProof,
    `Solution.Bridge
  ]
  let legacyImports := imported.filter fun name => forbidden.any (·.isPrefixOf name)
  unless legacyImports.isEmpty do
    throwError "Solution imports forbidden legacy proof/conversion modules: {legacyImports}"
  logInfo "Solution imports neither Challenge nor any forbidden legacy modules."

  let targets : Array Name := #[
    ``deque_ordinal_omega_ackermann_bound,
    ``prop_1_3_omega_properties,
    ``thm_1_4_main,
    ``lem_A_1_ack_basic,
    ``prop_A_2_lob_wainer,
    ``thm_2_2_mod1_reduction,
    ``lem_3_1_bst_projection,
    ``lem_3_2_cascade_equiv,
    ``lem_3_3_nested_keys,
    ``lem_3_4_spine_accounting,
    ``lem_3_5_emptying_sim,
    ``lem_3_6_folded_laws,
    ``thm_2_3_mod2_cascade,
    ``prop_4_1_right_reach,
    ``lem_4_2_preorder_global,
    ``lem_4_3_cascade_potentials,
    ``thm_2_5_mod3_pass,
    ``lem_5_1_tree_weights,
    ``lem_5_2_bucket_leaf,
    ``lem_5_3_bucket_b1,
    ``lem_5_4_bucket_b3_intra,
    ``lem_5_5_b3_post,
    ``lem_5_6_b3_escape,
    ``lem_5_7_b3_quotient,
    ``lem_5_8_b3_gaps,
    ``lem_5_9_bucket_b3_exit,
    ``lem_5_10_bucket_b2,
    ``thm_2_6_mod4_contraction,
    ``lem_6_1_build_scale_tree,
    ``prop_7_1_dyadic_collapse
  ]
  unless targets.size == 30 do
    throwError "Expected 30 target theorems, got {targets.size}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"
    logInfo m!"{name} uses only standard Lean axioms: {axioms}"
  logInfo m!"All {targets.size} theorems verified with standard Lean axioms only."
