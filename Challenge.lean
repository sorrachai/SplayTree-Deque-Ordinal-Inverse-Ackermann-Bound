module

public import Solution

/-!
# Ordinal-`ω` inverse-Ackermann deque challenge

The definitions are in `Challenge.Definitions`. `Solution` proves the bound for
those AlgoLib-based definitions, and this file retains the original target statement.
-/

public section

open SplayTree

/-- **Ordinal-`ω` Inverse-Ackermann Deque Bound for Splay Trees**:
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
  Solution.deque_ordinal_omega_ackermann_bound
