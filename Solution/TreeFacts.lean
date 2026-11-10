module

public import Challenge.Definitions
public import Mathlib

/-!
# Structural induction facts for AlgoLib binary search trees

Every tree and BST in this module is the existing AlgoLib/Mathlib type. The
auxiliary `ForallTree` predicate supports structural induction on a property of
all keys; it is equivalent to quantifying over AlgoLib's tree membership.
-/

@[expose] public section

namespace SplayDeque.Direct

variable {α : Type}

/-- A structurally indexed proof that every key of an AlgoLib tree satisfies `p`. -/
inductive ForallTree (p : α → Prop) : BinaryTree α → Prop
  | left : ForallTree p .nil
  | node (l : BinaryTree α) (key : α) (r : BinaryTree α) :
      ForallTree p l → p key → ForallTree p r →
      ForallTree p (.node key l r)

theorem forallTree_iff (p : α → Prop) (t : BinaryTree α) :
    ForallTree p t ↔ ∀ k ∈ t, p k := by
  induction t with
  | nil =>
    constructor
    · simp
    · intro _; exact .left
  | node k l r ihl ihr =>
    constructor
    · intro h x hx
      cases h with
      | node _ _ _ hl hk hr =>
        rcases BinaryTree.mem_node_iff.mp hx with h | h | h
        · simpa [h] using hk
        · exact ihl.mp hl x h
        · exact ihr.mp hr x h
    · intro h
      exact .node l k r (ihl.mpr (fun x hx => h x (.left hx)))
        (h k .here) (ihr.mpr (fun x hx => h x (.right hx)))

theorem valid_push_iff_forallTree [LinearOrder α] (t : BinaryTree α) (x : α) :
    (SplayTree.DequeOp.push x).Valid t ↔ ForallTree (x < ·) t :=
  (forallTree_iff _ _).symm

theorem valid_inject_iff_forallTree [LinearOrder α] (t : BinaryTree α) (x : α) :
    (SplayTree.DequeOp.inject x).Valid t ↔ ForallTree (· < x) t :=
  (forallTree_iff _ _).symm

theorem isBSTAux_of_mem_bounds [LinearOrder α] {t : BinaryTree α}
    (h : t.IsBST) (lb ub : Option α)
    (hlo : ∀ x ∈ t, lb.elim True (· < x))
    (hhi : ∀ x ∈ t, ub.elim True (x < ·)) :
    t.IsBSTAux lb ub := by
  induction t generalizing lb ub with
  | nil => exact .nil lb ub
  | node k l r ihl ihr =>
    refine .node (hlo k .here) (hhi k .here) ?_ ?_
    · exact ihl (BinaryTree.IsBST_left_of_IsBST h) lb (some k)
        (fun x hx => hlo x (.left hx))
        (fun _ hx => BinaryTree.lt_of_IsBST_left l k r h hx)
    · exact ihr (BinaryTree.IsBST_right_of_IsBST h) (some k) ub
        (fun _ hx => BinaryTree.gt_of_IsBST_right l k r h hx)
        (fun x hx => hhi x (.right hx))

theorem isBSTNil [LinearOrder α] : (BinaryTree.nil : BinaryTree α).IsBST :=
  .nil none none

/-- Build the existing AlgoLib invariant from subtree invariants and key bounds. -/
theorem isBSTNode [LinearOrder α] (key : α) (l r : BinaryTree α)
    (hlt : ForallTree (· < key) l) (hgt : ForallTree (key < ·) r)
    (hl : l.IsBST) (hr : r.IsBST) : (BinaryTree.node key l r).IsBST := by
  refine BinaryTree.IsBSTAux.node trivial trivial ?_ ?_
  · exact isBSTAux_of_mem_bounds hl none (some key) (by simp)
      ((forallTree_iff _ _).mp hlt)
  · exact isBSTAux_of_mem_bounds hr (some key) none
      ((forallTree_iff _ _).mp hgt) (by simp)

/-- Decompose AlgoLib's bounded invariant into ordinary subtree invariants. -/
theorem isBSTNode_iff [LinearOrder α] (key : α) (l r : BinaryTree α) :
    (BinaryTree.node key l r).IsBST ↔
      ForallTree (· < key) l ∧ ForallTree (key < ·) r ∧ l.IsBST ∧ r.IsBST := by
  constructor
  · intro h
    exact ⟨(forallTree_iff _ _).mpr (fun _ hx => BinaryTree.lt_of_IsBST_left l key r h hx),
      (forallTree_iff _ _).mpr (fun _ hx => BinaryTree.gt_of_IsBST_right l key r h hx),
      BinaryTree.IsBST_left_of_IsBST h, BinaryTree.IsBST_right_of_IsBST h⟩
  · rintro ⟨hlt, hgt, hl, hr⟩
    exact isBSTNode key l r hlt hgt hl hr

/-- Cases on an AlgoLib BST using unbounded child invariants. -/
@[elab_as_elim] theorem isBSTCases [LinearOrder α]
    {motive : (t : BinaryTree α) → t.IsBST → Prop}
    (left : motive .nil isBSTNil)
    (node : ∀ (key : α) (l r : BinaryTree α)
      (hlt : ForallTree (· < key) l) (hgt : ForallTree (key < ·) r)
      (hl : l.IsBST) (hr : r.IsBST),
      motive (.node key l r) (isBSTNode key l r hlt hgt hl hr)) :
    ∀ {t : BinaryTree α} (h : t.IsBST), motive t h := by
  intro t h
  cases t with
  | nil => exact left
  | node key l r =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBSTNode_iff key l r).mp h
    exact node key l r hlt hgt hl hr

/-- Induction on an AlgoLib BST using unbounded child invariants. -/
@[elab_as_elim] theorem isBSTRec [LinearOrder α]
    {motive : (t : BinaryTree α) → t.IsBST → Prop}
    (left : motive .nil isBSTNil)
    (node : ∀ (key : α) (l r : BinaryTree α)
      (hlt : ForallTree (· < key) l) (hgt : ForallTree (key < ·) r)
      (hl : l.IsBST) (hr : r.IsBST), motive l hl → motive r hr →
      motive (.node key l r) (isBSTNode key l r hlt hgt hl hr)) :
    ∀ {t : BinaryTree α} (h : t.IsBST), motive t h := by
  intro t
  induction t with
  | nil => intro h; exact left
  | node key l r ihl ihr =>
    intro h
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBSTNode_iff key l r).mp h
    exact node key l r hlt hgt hl hr (ihl hl) (ihr hr)

end SplayDeque.Direct

namespace BinaryTree.IsBST

variable {α : Type} [LinearOrder α]

/-- Constructor form of the AlgoLib invariant for an empty tree. -/
theorem left : (BinaryTree.nil : BinaryTree α).IsBST :=
  SplayDeque.Direct.isBSTNil

/-- Constructor form of the AlgoLib invariant from subtree key bounds. -/
theorem node (key : α) (l r : BinaryTree α)
    (hlt : SplayDeque.Direct.ForallTree (· < key) l)
    (hgt : SplayDeque.Direct.ForallTree (key < ·) r)
    (hl : l.IsBST) (hr : r.IsBST) : (BinaryTree.node key l r).IsBST :=
  SplayDeque.Direct.isBSTNode key l r hlt hgt hl hr

end BinaryTree.IsBST
