import AlgoLib.DataStructures.SplayTree.Complexity
import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat

namespace SplayDeque
open SplayTree
variable {α : Type}

-- 1. Extremal keys and splay-tree deque semantics on BinaryTree / BST
def minKey? : BinaryTree α → Option α
  | .nil => none
  | .node k l _ => match minKey? l with | none => some k | some m => some m
def maxKey? : BinaryTree α → Option α
  | .nil => none
  | .node k _ r => match maxKey? r with | none => some k | some m => some m

inductive DequeOp (α : Type) where
  | pop | push (key : α) | eject | inject (key : α)

def DequeOp.step [LinearOrder α] (t : BinaryTree α) : DequeOp α → BinaryTree α
  | .pop => match minKey? t with | none => .nil | some k => (splay t k).right
  | .eject => match maxKey? t with | none => .nil | some k => (splay t k).left
  | .push x => .node x .nil t
  | .inject x => .node x t .nil

noncomputable def DequeOp.cost [LinearOrder α] (t : BinaryTree α) : DequeOp α → ℝ
  | .pop => match minKey? t with | none => 0 | some k => splay.cost t k
  | .eject => match maxKey? t with | none => 0 | some k => splay.cost t k
  | .push _ | .inject _ => 0

def DequeOp.Valid [LinearOrder α] (t : BinaryTree α) : DequeOp α → Prop
  | .pop | .eject => t ≠ .nil
  | .push x => ∀ k ∈ t, x < k
  | .inject x => ∀ k ∈ t, k < x

def dequeSeq [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) : Fin (m + 1) → BinaryTree α :=
  fun i => Nat.recOn i.val init fun j acc =>
    if h : j < m then (ops ⟨j, h⟩).step acc else acc

def ValidDequeSeq [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) : Prop :=
  ∀ i : Fin m, (ops i).Valid (dequeSeq init ops i.castSucc)

noncomputable def dequeSequenceCost [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin m → DequeOp α) : ℝ :=
  ∑ i : Fin m, (ops i).cost (dequeSeq init ops i.castSucc)

def popCount {m : ℕ} (ops : Fin m → DequeOp α) : ℕ :=
  (Finset.univ.filter fun i => ops i matches .pop).card
def ejectCount {m : ℕ} (ops : Fin m → DequeOp α) : ℕ :=
  (Finset.univ.filter fun i => ops i matches .eject).card

-- 2. Ackermann hierarchy A_i(j), star-iterates α_r, and level-ω inverse α_ω
def ackermannStep (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1 | 1 => f 2 | j + 2 => f (ackermannStep f (j + 1))
def ackermann : ℕ → ℕ → ℕ
  | 0 => fun j => 2 * j | 1 => fun j => 2 ^ j
  | i + 2 => ackermannStep (ackermann (i + 1))

noncomputable def alpha0 (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}

def starIterate (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n ≤ 4 then 1 else if _h : f n < n then 1 + starIterate f (f n) else 1
termination_by n

noncomputable def alphaHierarchy : ℕ → ℕ → ℕ
  | 0 => alpha0 | r + 1 => starIterate (alphaHierarchy r)
noncomputable def alphaOmega (n : ℕ) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ alphaHierarchy r n ≤ 2}

-- 3. Main Theorem (Theorem 1.4)
theorem thm_1_4_main :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type} [LinearOrder α] (n m : ℕ)
        (init : BST α) (ops : Fin m → DequeOp α),
      init.tree.num_nodes = n → ValidDequeSeq init.tree ops →
      dequeSequenceCost init.tree ops ≤ C * ((n : ℝ) + (m : ℝ) +
        (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) +
        (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ)) := by
  sorry

end SplayDeque
