module

public import Solution.Bridge
public import Solution.LegacyProof

/-!
# Solution of the AlgoLib-based challenge

The original long proof is checked in `Solution.LegacyProof`. The theorems in
`Solution.Bridge` transfer its bound to the exact definitions used by the new
challenge, including AlgoLib's `BinaryTree`, `BST`, and splay rotation cost.
-/

public section

namespace Solution

open SplayTree SplayDeque.Bridge

/-- The supplied explicit bound, transported to the AlgoLib definitions. -/
theorem deque_ordinal_omega_explicit_bound
    (n m : ℕ) (init : BST ℤ) (ops : Fin m → DequeOp ℤ)
    (hn : init.tree.num_nodes = n) (hvalid : ValidDequeSeq init.tree ops) :
    dequeSequenceCost init.tree ops ≤
      5757 * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) := by
  have h := SplayDeque.Legacy.deque_ordinal_omega_explicit_bound n m (toLegacyBST init)
    (fun i => toLegacyOp (ops i)) (by simpa [toLegacyBST] using hn)
    (toLegacy_validSeq init.tree ops hvalid)
  simpa only [toLegacyBST, toLegacy_sequenceCost, ordinalOmegaInvAckermann_eq] using h

/-- The exact target statement of the new challenge, with a proved constant. -/
theorem deque_ordinal_omega_ackermann_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (init : BST ℤ) (ops : Fin m → DequeOp ℤ),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) :=
  ⟨5757, by positivity, deque_ordinal_omega_explicit_bound⟩

end Solution
