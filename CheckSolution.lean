module

import SolutionMain
import SolutionHelpers
import Lean.Util.CollectAxioms

/-! Audit the dependency closure and kernel axioms of all 30 theorems across
`SolutionMain` (2 main theorems) and `SolutionHelpers` (28 helper theorems),
independently of the `ChallengeMain` and `ChallengeHelpers` blueprints. -/

open Lean Elab Command in
run_elab do
  let imported := (← getEnv).allImportedModuleNames
  for bad in #[`ChallengeMain, `ChallengeHelpers, `Challenge] do
    if imported.contains bad then
      throwError "Solution transitively imports blueprint module {bad}!"
  let forbidden : Array Name := #[
    `Solution.LegacyDefinitions,
    `Solution.LegacyProof,
    `Solution.Bridge
  ]
  let legacyImports := imported.filter fun name => forbidden.any (·.isPrefixOf name)
  unless legacyImports.isEmpty do
    throwError "Solution imports forbidden legacy proof/conversion modules: {legacyImports}"
  logInfo "Neither SolutionMain nor SolutionHelpers imports ChallengeMain/ChallengeHelpers or legacy modules."

  let targets : Array Name := #[
    ``thm_1_4_main,
    ``deque_ordinal_omega_ackermann_bound,
    ``prop_1_3_omega_properties,
    ``thm_2_2_mod1_reduction,
    ``lem_2_3_bst_projection,
    ``lem_2_4_cascade_equiv,
    ``lem_2_5_nested_keys,
    ``lem_2_6_spine_accounting,
    ``lem_2_7_emptying_sim,
    ``lem_2_8_folded_laws,
    ``thm_3_1_mod2_cascade,
    ``prop_3_2_right_reach,
    ``lem_3_3_preorder_global,
    ``lem_3_4_cascade_potentials,
    ``thm_4_2_mod3_pass,
    ``lem_4_3_tree_weights,
    ``lem_4_4_bucket_leaf,
    ``lem_4_5_bucket_b1,
    ``lem_4_6_bucket_b3_intra,
    ``lem_4_7_b3_post,
    ``lem_4_8_b3_escape,
    ``lem_4_9_b3_quotient,
    ``lem_4_10_b3_gaps,
    ``lem_4_11_bucket_b3_exit,
    ``lem_4_12_bucket_b2,
    ``thm_5_1_mod4_contraction,
    ``lem_5_2_build_scale_tree,
    ``prop_6_1_dyadic_collapse,
    ``lem_A_1_ack_basic,
    ``prop_A_2_lob_wainer
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
