module

public import Challenge.MainDefinitions

/-!
# Ordinal-`ω` Inverse-Ackermann Deque Bound for Splay Trees — Main Challenge

Minimal, self-contained specification of the paper's main upper bound on splay-tree
deque executions (`main_v2.tex`, Theorem 1.4), importing **only**
`Challenge.MainDefinitions` (with no helper structures or intermediate proof
concepts):

1. `thm_1_4_main`: Theorem 1.4 of `main_v2.tex` — the polymorphic, deletion-sensitive
   bound `Rot(T_0, S) ≤ C (n + m + d_L α_ω(max(d_L, 1)) + d_R α_ω(max(d_R, 1)))` over
   any `LinearOrder α` and all `n, m ≥ 0`;
2. `deque_ordinal_omega_ackermann_bound`: the standalone `O((m + n) α_ω(m + n))` bound
   on `BST ℤ` from the original repository challenge.

All 28 intermediate propositions, lemmas, and reduction theorems across Sections 1–6
and Appendix A of `main_v2.tex` are specified separately in `ChallengeHelpers.lean`.
-/

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
            (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ)) := by
  sorry

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
          C * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) := by
  sorry

end
