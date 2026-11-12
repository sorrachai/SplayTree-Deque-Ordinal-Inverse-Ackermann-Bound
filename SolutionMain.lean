module

public import Challenge.MainDefinitions
public import Solution.Ackermann
public import Solution.BSTProjections
public import Solution.FoldedLaws
public import Solution.TamariPreorder
public import Solution.Contraction
public import Solution.ScaleWeights
public import Solution.Cascades
public import Solution.KeyAssignmentSpine
public import Solution.EmptyingMod1
public import Solution.BucketLeafB1
public import Solution.BucketB3PostEscape
public import Solution.BucketB3GapsExit
public import Solution.BucketB2Pass
public import Solution.TopAssembly

/-!
# Ordinal-`ω` Inverse-Ackermann Deque Bound for Splay Trees — Main Solution

Proves both main challenge theorems specified in `ChallengeMain.lean` (`thm_1_4_main`,
matching Theorem 1.4 of `main_v2.tex`, and `deque_ordinal_omega_ackermann_bound`) by
wiring Layers `0 → 1 → 2 → 3 → 4 → 5` of `Solution.*`, without importing
`ChallengeMain` or `ChallengeHelpers`.
-/

section Wiring

-- Layer 0: Leaf Modules
private abbrev w_lem_A_1 := Solution.Ackermann.lem_A_1_ack_basic
private abbrev w_prop_1_3 := Solution.Ackermann.prop_1_3_omega_properties
private abbrev w_lem_2_3 := @Solution.BSTProjections.lem_3_1_bst_projection
private abbrev w_lem_2_4 := @Solution.BSTProjections.lem_3_2_cascade_equiv
private abbrev w_prop_3_2 := Solution.TamariPreorder.prop_4_1_right_reach
private abbrev w_lem_2_8 := Solution.FoldedLaws.lem_3_6_folded_laws

-- Layer 1: `Contraction`, `ScaleWeights`, `Cascades`, `KeyAssignmentSpine`
private abbrev w_thm_5_1 := Solution.Contraction.thm_2_6_mod4_contraction_of_deps w_lem_A_1
private abbrev w_lem_4_3 := Solution.ScaleWeights.lem_5_1_tree_weights
private abbrev w_thm_3_1 := Solution.Cascades.thm_2_3_mod2_cascade
private abbrev w_lem_2_5 := @Solution.KeyAssignmentSpine.lem_3_3_nested_keys
private abbrev w_lem_2_6 {α : Type} [LinearOrder α] :=
  Solution.KeyAssignmentSpine.lem_3_4_spine_accounting (@w_lem_2_3) (@w_lem_2_4) (α := α)

-- Layer 2: `EmptyingMod1`, `BucketLeafB1`, `BucketB3PostEscape`
private abbrev w_thm_2_2 :=
  Solution.EmptyingMod1.thm_2_2_mod1_reduction (@w_lem_2_4) (@w_lem_2_5) (@w_lem_2_6)
private abbrev w_lem_4_4 {M : ℕ} :=
  Solution.BucketLeafB1.lem_5_2_bucket_leaf (@w_lem_2_8) (M := M)
private abbrev w_lem_4_5 :=
  Solution.BucketLeafB1.lem_5_3_bucket_b1 (@w_lem_2_8) (@w_lem_4_3)
private abbrev w_lem_4_6 :=
  Solution.BucketLeafB1.lem_5_4_bucket_b3_intra (@w_lem_2_8) (@w_lem_4_3)
private abbrev w_lem_4_7 := Solution.BucketB3PostEscape.lem_5_5_b3_post
private abbrev w_lem_4_8 :=
  Solution.BucketB3PostEscape.lem_5_6_b3_escape (@w_lem_2_8) (@w_lem_4_3)
private abbrev w_lem_4_9 :=
  Solution.BucketB3PostEscape.lem_5_7_b3_quotient (@w_lem_2_3)

-- Layer 3: `BucketB3GapsExit`
private abbrev w_lem_4_11 :=
  Solution.BucketB3GapsExit.lem_5_9_bucket_b3_exit
    (@w_lem_A_1) (@w_lem_2_3) (@w_lem_2_8) (@w_prop_3_2) (@w_lem_4_3) (@w_lem_4_4)
    (@w_lem_4_5) (@w_lem_4_6) (@w_lem_4_7) (@w_lem_4_8) (@w_lem_4_9)

-- Layer 4: `BucketB2Pass`
private abbrev w_thm_4_2 :=
  Solution.BucketB2Pass.thm_2_5_mod3_pass
    (@w_lem_2_8) (@w_thm_3_1) (@w_lem_4_3) (@w_lem_4_4) (@w_lem_4_5) (@w_lem_4_11)

-- Layer 5: `TopAssembly`
private abbrev w_thm_1_4 :=
  Solution.TopAssembly.thm_1_4_main w_thm_2_2 w_thm_4_2 w_thm_5_1 w_lem_A_1
private abbrev w_deque_bound :=
  Solution.TopAssembly.deque_ordinal_omega_ackermann_bound_of_thm_1_4
    w_thm_1_4 w_prop_1_3 w_lem_A_1

end Wiring

public section

open SplayTree

/-- **Theorem 1.4** (`thm:main`, Main Theorem — Deletion-Sensitive Bound):
There exists an absolute constant `C > 0` such that for every linear order `α`, every
`n`-node BST `init : BST α` (`n ≥ 0`), and every valid `m`-operation splay-tree deque
sequence `ops` (`m ≥ 0`) with `d_L = popCount ops` and `d_R = ejectCount ops`,
`Rot(T_0, S) ≤ C (n + m + d_L α_ω(max(d_L, 1)) + d_R α_ω(max(d_R, 1)))`. -/
theorem thm_1_4_main :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [LinearOrder α] (n m : ℕ) (init : BST α) (ops : Fin m → DequeOp α),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((n : ℝ) + (m : ℝ) +
            (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) +
            (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ)) :=
  w_thm_1_4

/-- **Ordinal-`ω` Inverse-Ackermann Deque Bound for Splay Trees** (original benchmark form):
There exists an absolute constant `C > 0` such that for any initial binary search tree `init`
with `n` nodes and any valid sequence `ops` of `m` deque operations (`pop`, `push`, `eject`,
`inject`), the total rotation cost `dequeSequenceCost init.tree ops` is at most
`C * (m + n) * ordinalOmegaInvAckermann (m + n)`. -/
theorem deque_ordinal_omega_ackermann_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (init : BST ℤ) (ops : Fin m → DequeOp ℤ),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) :=
  w_deque_bound

end
