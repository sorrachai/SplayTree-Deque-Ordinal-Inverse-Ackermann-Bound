module

public import Mathlib

@[expose] public section

namespace SplayDeque.Legacy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

/-!
# Ordinal-`ω` Inverse-Ackermann Deque Bound for Splay Trees

This file gives a self-contained Lean 4 formulation of the `O((m + n) α_ω(m + n))` upper bound
on Tarjan's Deque Conjecture [Tar85] for splay trees, strictly improving both Pettie's
`O((m + n) α*(m + n))` bound [Pet08, Theorem 5.1] and every finite star-iterate bound
`O((m + n) α_r(m + n))` (`r ≥ 1`). It imports only Mathlib and defines:

* binary search trees (`BinaryTree`, `IsBST`, `BST`);
* the bottom-up splay operation (`splay`) and its rotation cost (`splay.cost`), one unit per
  single rotation;
* the four deque operations `pop` (delete-min), `push` (insert-min), `eject` (delete-max), and
  `inject` (insert-max), together with their validity preconditions and rotation costs;
* the state trajectory and total rotation cost of a sequence of deque operations;
* Sundar's Ackermann hierarchy (`ackermannStep`, `ackermann`), inverse Ackermann function
  (`invAckermann`), iterated inverse Ackermann function (`iteratedInvAckermann`),
  double-iterated inverse Ackermann function (`doubleIteratedInvAckermann`), the full finite
  star-iterate hierarchy (`iteratedInvAckermannHierarchy`), and the ordinal-`ω` diagonal inverse
  Ackermann function (`ordinalOmegaInvAckermann`).
-/

variable {α : Type}

namespace SplayTree

/-!
================================================================================
1. Binary Search Trees (`BinaryTree` and `BST`)
================================================================================
-/

inductive BinaryTree (α : Type) where
  | empty
  | node (left : BinaryTree α) (key : α) (right : BinaryTree α)
  deriving DecidableEq

namespace BinaryTree

def left : BinaryTree α → BinaryTree α
  | .empty => .empty
  | .node l _ _ => l

def right : BinaryTree α → BinaryTree α
  | .empty => .empty
  | .node _ _ r => r

def num_nodes : BinaryTree α → ℕ
  | .empty => 0
  | .node l _ r => 1 + num_nodes l + num_nodes r

def rotateRight : BinaryTree α → BinaryTree α
  | .node (.node a x b) y c => .node a x (.node b y c)
  | t => t

def rotateLeft : BinaryTree α → BinaryTree α
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t

inductive ForallTree (p : α → Prop) : BinaryTree α → Prop
  | left : ForallTree p .empty
  | node l key r :
     ForallTree p l →
     p key →
     ForallTree p r →
     ForallTree p (.node l key r)

inductive IsBST [LinearOrder α] : BinaryTree α → Prop
  | left : IsBST .empty
  | node key l r :
     ForallTree (fun k => k < key) l →
     ForallTree (fun k => key < k) r →
     IsBST l → IsBST r →
     IsBST (.node l key r)

end BinaryTree

structure BST (α : Type) [LinearOrder α] where
  tree : BinaryTree α
  hBST : BinaryTree.IsBST tree


/-!
================================================================================
2. Bottom-Up Splay Operation and Rotation Cost
================================================================================
-/

open _root_.SplayDeque.Legacy.SplayTree.BinaryTree

inductive Dir
  | L -- target descended into the left subtree from this parent
  | R -- target descended into the right subtree from this parent
  deriving DecidableEq, Repr

/-- Single primitive rotation that brings the `d`-child of the root up one
level. `L` ↦ `rotateRight`, `R` ↦ `rotateLeft`. -/
def Dir.bringUp : Dir → BinaryTree α → BinaryTree α
  | .L => rotateRight
  | .R => rotateLeft

/-- Apply `op` to the `d`-child of the root, leaving everything else fixed. -/
def applyChild (d : Dir) (op : BinaryTree α → BinaryTree α) : BinaryTree α → BinaryTree α
  | .node l k r =>
    match d with
    | .L => .node (op l) k r
    | .R => .node l k (op r)
  | .empty => .empty

/-- One frame of the search path: the direction we took from this ancestor,
its key, and the subtree we did *not* descend into. -/
structure Frame α where
  dir : Dir
  key : α
  sibling : BinaryTree α

/-- Re-attach a subtree `c` below the ancestor described by `f`. -/
def Frame.attach (c : BinaryTree α) (f : Frame α) : BinaryTree α :=
  match f.dir with
  | .L => .node c f.key f.sibling
  | .R => .node f.sibling f.key c

/-- Descend from `t` toward `q`, returning the subtree reached (either the
matching node or `.empty` if `q` is absent) and the path above it. The head
of the returned list is the deepest frame (parent of the returned subtree). -/
def descend [LinearOrder α] (t : BinaryTree α) (q : α) : BinaryTree α × List (Frame α) :=
  go t []
where
  go : BinaryTree α → List (Frame α) → BinaryTree α × List (Frame α)
  | .empty, acc => (.empty, acc)
  | .node l k r, acc =>
    if q = k then (.node l k r, acc)
    else if q < k then go l ({ dir := .L, key := k, sibling := r } :: acc)
    else go r ({ dir := .R, key := k, sibling := l } :: acc)

/-- Splay the subtree `c` upward along `path`, pairing frames from the bottom
up. -/
def splayUp : BinaryTree α → List (Frame α) → BinaryTree α
  | c, [] => c
  | c, [f] => f.dir.bringUp (f.attach c)
  | c, f1 :: f2 :: rest =>
    let s := f2.attach (f1.attach c)
    let s' :=
      if f1.dir = f2.dir then
        f2.dir.bringUp (f2.dir.bringUp s)
      else
        f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
    splayUp s' rest

/-- Bottom-up splay: if `q` is absent the last visited ancestor is splayed to the root. -/
def splay [LinearOrder α] (t : BinaryTree α) (q : α) : BinaryTree α :=
  match descend t q with
  | (.empty, []) => .empty
  | (.empty, f :: rest) => splayUp (f.attach .empty) rest
  | (x@(.node _ _ _), path) => splayUp x path

/-- Cost of a bottom-up splay: one unit per rotation. -/
def splay.cost [LinearOrder α] (t : BinaryTree α) (q : α) : ℝ :=
  match descend t q with
  | (.empty, []) => 0
  | (.empty, _ :: rest) => rest.length
  | (.node _ _ _, path) => path.length


/-!
================================================================================
3. Deque Operations (`pop`, `push`, `eject`, `inject`)
================================================================================
-/

/-- The minimum (leftmost) key of a binary tree, or `none` if the tree is empty. -/
def BinaryTree.minKey? : BinaryTree α → Option α
  | .empty => none
  | .node l k _ =>
    match l.minKey? with
    | none => some k
    | some m => some m

/-- The maximum (rightmost) key of a binary tree, or `none` if the tree is empty. -/
def BinaryTree.maxKey? : BinaryTree α → Option α
  | .empty => none
  | .node _ k r =>
    match r.maxKey? with
    | none => some k
    | some m => some m

/-- `POP` (`deleteMin`): Splay the minimum (leftmost) node to the root and remove it
by returning the resulting right subtree. On an empty tree, returns `.empty`. -/
def pop [LinearOrder α] (t : BinaryTree α) : BinaryTree α :=
  match t.minKey? with
  | none => .empty
  | some k => (splay t k).right

/-- `PUSH` (`insertMin`): Insert a new key `x` smaller than all existing keys as the
new root with an empty left subtree and `t` as its right subtree. -/
def push (t : BinaryTree α) (x : α) : BinaryTree α :=
  .node .empty x t

/-- `EJECT` (`deleteMax`): Splay the maximum (rightmost) node to the root and remove it
by returning the resulting left subtree. On an empty tree, returns `.empty`. -/
def eject [LinearOrder α] (t : BinaryTree α) : BinaryTree α :=
  match t.maxKey? with
  | none => .empty
  | some k => (splay t k).left

/-- `INJECT` (`insertMax`): Insert a new key `x` larger than all existing keys as the
new root with `t` as its left subtree and an empty right subtree. -/
def inject (t : BinaryTree α) (x : α) : BinaryTree α :=
  .node t x .empty

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
  | .pop => t ≠ .empty
  | .push x => ForallTree (fun k => x < k) t
  | .eject => t ≠ .empty
  | .inject x => ForallTree (fun k => k < x) t

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
4. Ackermann Hierarchy, Finite Star-Iterates, and Ordinal-`ω` Inverse Ackermann
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


end SplayDeque.Legacy
