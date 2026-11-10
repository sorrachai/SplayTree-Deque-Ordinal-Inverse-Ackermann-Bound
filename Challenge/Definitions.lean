module

public import AlgoLib.DataStructures.SplayTree.Complexity
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Lattice.Nat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

/-!
# Ordinal-`ω` Inverse-Ackermann Deque Bound for Splay Trees

This file formulates the supplied splay-tree deque challenge using AlgoLib's
`BinaryTree`, `BST`, bottom-up `SplayTree.splay`, and rotation cost `SplayTree.splay.cost`.
It defines the deque operations, valid operation sequences, and the inverse-Ackermann
hierarchy needed for the target statement.

The target theorem is stated in `Challenge.lean`; its proof is supplied by
`Solution.lean`. This module contains only the shared definitions.
-/

@[expose] public section

variable {α : Type}

/-! ## 1. Deque operations on AlgoLib binary trees -/

namespace BinaryTree

/-- The minimum (leftmost) key of a binary tree, or `none` if the tree is empty. -/
def minKey? : BinaryTree α → Option α
  | .nil => none
  | .node k l _ =>
    match l.minKey? with
    | none => some k
    | some m => some m

/-- The maximum (rightmost) key of a binary tree, or `none` if the tree is empty. -/
def maxKey? : BinaryTree α → Option α
  | .nil => none
  | .node k _ r =>
    match r.maxKey? with
    | none => some k
    | some m => some m

end BinaryTree

namespace SplayTree

open BinaryTree

/-- `POP` (`deleteMin`): Splay the minimum (leftmost) node to the root and remove it
by returning the resulting right subtree. On an empty tree, returns `.nil`. -/
def pop [LinearOrder α] (t : BinaryTree α) : BinaryTree α :=
  match t.minKey? with
  | none => .nil
  | some k => (splay t k).right

/-- `PUSH` (`insertMin`): Insert a new key `x` smaller than all existing keys as the
new root with an empty left subtree and `t` as its right subtree. -/
def push (t : BinaryTree α) (x : α) : BinaryTree α :=
  .node x .nil t

/-- `EJECT` (`deleteMax`): Splay the maximum (rightmost) node to the root and remove it
by returning the resulting left subtree. On an empty tree, returns `.nil`. -/
def eject [LinearOrder α] (t : BinaryTree α) : BinaryTree α :=
  match t.maxKey? with
  | none => .nil
  | some k => (splay t k).left

/-- `INJECT` (`insertMax`): Insert a new key `x` larger than all existing keys as the
new root with `t` as its left subtree and an empty right subtree. -/
def inject (t : BinaryTree α) (x : α) : BinaryTree α :=
  .node x t .nil

/-- Rotation cost of `pop`: equals the rotation cost of splaying the minimum key
(or `0` if the tree is empty). -/
noncomputable def popCost [LinearOrder α] (t : BinaryTree α) : ℝ :=
  match t.minKey? with
  | none => 0
  | some k => splay.cost t k

/-- Rotation cost of `eject`: equals the rotation cost of splaying the maximum key
(or `0` if the tree is empty). -/
noncomputable def ejectCost [LinearOrder α] (t : BinaryTree α) : ℝ :=
  match t.maxKey? with
  | none => 0
  | some k => splay.cost t k

/-- A single deque operation on keys of type `α`. -/
inductive DequeOp (α : Type) where
  | pop : DequeOp α
  | push (key : α) : DequeOp α
  | eject : DequeOp α
  | inject (key : α) : DequeOp α
  deriving DecidableEq, Repr

/-- Apply a single `DequeOp` to a `BinaryTree`. -/
def DequeOp.step [LinearOrder α] (t : BinaryTree α) : DequeOp α → BinaryTree α
  | .pop => SplayTree.pop t
  | .push x => SplayTree.push t x
  | .eject => SplayTree.eject t
  | .inject x => SplayTree.inject t x

/-- Rotation cost of a single `DequeOp` on `t`. `push` and `inject` perform no rotations
(cost `0`); `pop` and `eject` pay the rotation cost of splaying the extremum to the root. -/
noncomputable def DequeOp.cost [LinearOrder α] (t : BinaryTree α) : DequeOp α → ℝ
  | .pop => popCost t
  | .push _ => 0
  | .eject => ejectCost t
  | .inject _ => 0

/-- Precondition for a `DequeOp` to be a valid deque operation on `t`:
* `pop` and `eject` require `t` to be non-empty;
* `push x` requires `x` to be strictly smaller than all keys currently in `t`;
* `inject x` requires `x` to be strictly larger than all keys currently in `t`. -/
def DequeOp.Valid [LinearOrder α] (t : BinaryTree α) : DequeOp α → Prop
  | .pop => t ≠ .nil
  | .push x => ∀ k ∈ t, x < k
  | .eject => t ≠ .nil
  | .inject x => ∀ k ∈ t, k < x

/-- State trajectory of the tree across a sequence of `m` deque operations. -/
def dequeSeq [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) : Fin (m + 1) → BinaryTree α :=
  fun i => Nat.recOn i.val init (fun j acc =>
    if h : j < m then (ops ⟨j, h⟩).step acc else acc)

/-- A sequence of `m` deque operations is valid from `init` if every step's operation
is valid on the current tree state. -/
def ValidDequeSeq [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) : Prop :=
  ∀ i : Fin m, (ops i).Valid (dequeSeq init ops i.castSucc)

/-- Total rotation cost of executing a sequence of `m` deque operations starting from `init`. -/
noncomputable def dequeSequenceCost [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) : ℝ :=
  ∑ i : Fin m, (ops i).cost (dequeSeq init ops i.castSucc)


/-!
================================================================================
2. Ackermann Hierarchy, Finite Star-Iterates, and Ordinal-`ω` Inverse Ackermann
================================================================================
-/

/-- Given the previous level `f = A_{i-1}`, compute `A_i(j)` (Sundar 1992, Section 1.2):
* `A_i(0) = 1` (by convention)
* `A_i(1) = f 2`
* `A_i(j + 1) = f (A_i(j))` for `j ≥ 1`. -/
def ackermannStep (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => f 2
  | j + 2 => f (ackermannStep f (j + 1))

/-- Sundar's Ackermann hierarchy `A_i(j)` (Sundar 1992, Section 1.2):
* `A_0(j) = 2 * j`
* `A_1(j) = 2 ^ j`
* `A_{i+2}(1) = A_{i+1}(2)` (with `A_{i+2}(0) = 1` by convention)
* `A_{i+2}(j+1) = A_{i+1}(A_{i+2}(j))` for `j ≥ 1`. -/
def ackermann : ℕ → ℕ → ℕ
  | 0 => fun j => 2 * j
  | 1 => fun j => 2 ^ j
  | i + 2 => ackermannStep (ackermann (i + 1))

/-- Sundar's inverse Ackermann function `ᾱ(n) = min {k ≥ 1 | A_k(1) ≥ n}`
(Sundar 1992, Section 1.2). -/
noncomputable def invAckermann (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}

/-- Iterated inverse Ackermann function `α*(n) = min {i ≥ 1 | ᾱ^[i](n) ≤ 2}` (Pettie 2008,
Section 3). -/
noncomputable def iteratedInvAckermann (n : ℕ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ (invAckermann^[i] n) ≤ 2}

/-- Double-iterated inverse Ackermann function `(α*)*(n) = min {i ≥ 1 | (α*)^[i](n) ≤ 2}`:
the minimum number of applications of `iteratedInvAckermann` (`α*`) required to map `n` to at
most `2` (applying Pettie's iteration operator `f*(n) = min {i ≥ 1 | f^[i](n) ≤ 2}` to `α*`). -/
noncomputable def doubleIteratedInvAckermann (n : ℕ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ (iteratedInvAckermann^[i] n) ≤ 2}

/-- Full finite star-iterate hierarchy `α_r(n)` (`r : ℕ`), applying Pettie's star operator
`f ↦ (fun n => min {i ≥ 1 | f^[i](n) ≤ 2})` `r` times to `invAckermann`:
* `iteratedInvAckermannHierarchy 0 = invAckermann` (`rfl`),
* `iteratedInvAckermannHierarchy 1 = iteratedInvAckermann` (`rfl`),
* `iteratedInvAckermannHierarchy 2 = doubleIteratedInvAckermann` (`rfl`). -/
noncomputable def iteratedInvAckermannHierarchy : ℕ → ℕ → ℕ
  | 0 => invAckermann
  | r + 1 => fun n => sInf {i : ℕ | 1 ≤ i ∧ ((iteratedInvAckermannHierarchy r)^[i] n) ≤ 2}

/-- Ordinal-`ω` diagonal inverse Ackermann function
`α_ω(n) = min {r ≥ 1 | α_r(n) ≤ 2}`, strictly dominating every finite star-iterate `α_r(n)`
(`α_ω(n) = o(α_r(n))` as `n → ∞` for every fixed `r ≥ 1`). -/
noncomputable def ordinalOmegaInvAckermann (n : ℕ) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ iteratedInvAckermannHierarchy r n ≤ 2}

end SplayTree
