module

public import Solution.DirectProof

/-!
# Solution of the AlgoLib-based challenge

`Solution.DirectProof` establishes the bound directly for AlgoLib's `BinaryTree`,
`BST`, splay operations, and the definitions in `Challenge.Definitions`.
-/

public section

namespace Solution

open SplayTree

/-- The explicit bound proved directly on the AlgoLib definitions. -/
theorem deque_ordinal_omega_explicit_bound
    (n m : ℕ) (init : BST ℤ) (ops : Fin m → DequeOp ℤ)
    (hn : init.tree.num_nodes = n) (hvalid : ValidDequeSeq init.tree ops) :
    dequeSequenceCost init.tree ops ≤
      5757 * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) :=
  SplayDeque.Direct.deque_ordinal_omega_explicit_bound n m init ops hn hvalid

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

open SplayTree

/-- The completed challenge, with the same name and statement as the independent
reference in `Challenge.lean`. Import `Solution` to use this proved theorem. -/
theorem deque_ordinal_omega_ackermann_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (init : BST ℤ) (ops : Fin m → DequeOp ℤ),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) :=
  Solution.deque_ordinal_omega_ackermann_bound
