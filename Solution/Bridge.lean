module

public import Challenge.Definitions
public import Solution.LegacyDefinitions

/-!
# Transport from AlgoLib to the supplied proof model

The public challenge uses AlgoLib's `BinaryTree`, `BST`, and splay operations.
This module verifies that the original proof model represents the same trees,
operations, valid sequences, and rotation costs. No bound is assumed here.
-/

@[expose] public section

namespace SplayDeque.Bridge

variable {α : Type}

def toLegacy : BinaryTree α → Legacy.SplayTree.BinaryTree α
  | .nil => .empty
  | .node k l r => .node (toLegacy l) k (toLegacy r)

@[simp] theorem toLegacy_num_nodes (t : BinaryTree α) :
    (toLegacy t).num_nodes = t.num_nodes := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp [toLegacy, Legacy.SplayTree.BinaryTree.num_nodes, BinaryTree.num_nodes, ihl, ihr]

@[simp] theorem toLegacy_empty_iff (t : BinaryTree α) :
    toLegacy t = .empty ↔ t = .nil := by
  cases t <;> simp [toLegacy]

@[simp] theorem toLegacy_left (t : BinaryTree α) :
    toLegacy t.left = (toLegacy t).left := by cases t <;> rfl

@[simp] theorem toLegacy_right (t : BinaryTree α) :
    toLegacy t.right = (toLegacy t).right := by cases t <;> rfl

@[simp] theorem toLegacy_minKey (t : BinaryTree α) :
    (toLegacy t).minKey? = t.minKey? := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [toLegacy, BinaryTree.minKey?, Legacy.SplayTree.BinaryTree.minKey?, ihl]
    rfl

@[simp] theorem toLegacy_maxKey (t : BinaryTree α) :
    (toLegacy t).maxKey? = t.maxKey? := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [toLegacy, BinaryTree.maxKey?, Legacy.SplayTree.BinaryTree.maxKey?, ihr]
    rfl

theorem forallTree_iff (p : α → Prop) (t : BinaryTree α) :
    Legacy.SplayTree.BinaryTree.ForallTree p (toLegacy t) ↔ ∀ k ∈ t, p k := by
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
      exact .node _ _ _ (ihl.mpr (fun x hx => h x (.left hx)))
        (h k .here) (ihr.mpr (fun x hx => h x (.right hx)))

theorem toLegacy_isBST [LinearOrder α] (t : BinaryTree α) (h : t.IsBST) :
    Legacy.SplayTree.BinaryTree.IsBST (toLegacy t) := by
  induction t with
  | nil => exact .left
  | node k l r ihl ihr =>
    exact .node k _ _
      ((forallTree_iff _ l).mpr (fun x hx => BinaryTree.lt_of_IsBST_left l k r h hx))
      ((forallTree_iff _ r).mpr (fun x hx => BinaryTree.gt_of_IsBST_right l k r h hx))
      (ihl (BinaryTree.IsBST_left_of_IsBST h))
      (ihr (BinaryTree.IsBST_right_of_IsBST h))

def toLegacyBST [LinearOrder α] (t : BST α) : Legacy.SplayTree.BST α :=
  ⟨toLegacy t.tree, toLegacy_isBST t.tree t.hBST⟩

def toLegacyDir : SplayTree.Dir → Legacy.SplayTree.Dir
  | .L => .L
  | .R => .R

@[simp] theorem toLegacyDir_eq_iff (a b : SplayTree.Dir) :
    toLegacyDir a = toLegacyDir b ↔ a = b := by
  cases a <;> cases b <;> simp [toLegacyDir]

def toLegacyFrame (f : SplayTree.Frame α) : Legacy.SplayTree.Frame α :=
  ⟨toLegacyDir f.dir, f.key, toLegacy f.sibling⟩

@[simp] theorem toLegacy_rotateRight (t : BinaryTree α) :
    toLegacy t.rotateRight = (toLegacy t).rotateRight := by
  cases t with
  | nil => rfl
  | node k l r => cases l <;> rfl

@[simp] theorem toLegacy_rotateLeft (t : BinaryTree α) :
    toLegacy t.rotateLeft = (toLegacy t).rotateLeft := by
  cases t with
  | nil => rfl
  | node k l r => cases r <;> rfl

@[simp] theorem toLegacy_bringUp (d : SplayTree.Dir) (t : BinaryTree α) :
    toLegacy (d.bringUp t) = (toLegacyDir d).bringUp (toLegacy t) := by
  cases d <;> simp [SplayTree.Dir.bringUp, toLegacyDir,
    Legacy.SplayTree.Dir.bringUp]

@[simp] theorem toLegacy_attach (f : SplayTree.Frame α) (t : BinaryTree α) :
    toLegacy (f.attach t) = (toLegacyFrame f).attach (toLegacy t) := by
  cases f with
  | mk d k s => cases d <;> rfl

@[simp] theorem toLegacy_applyChild (d e : SplayTree.Dir) (t : BinaryTree α) :
    toLegacy (SplayTree.applyChild d e.bringUp t) =
      Legacy.SplayTree.applyChild (toLegacyDir d) (toLegacyDir e).bringUp (toLegacy t) := by
  cases t <;> cases d <;>
    simp [SplayTree.applyChild, Legacy.SplayTree.applyChild, toLegacy, toLegacyDir]

@[simp] theorem toLegacy_splayUp (t : BinaryTree α) (path : List (SplayTree.Frame α)) :
    toLegacy (SplayTree.splayUp t path) =
      Legacy.SplayTree.splayUp (toLegacy t) (path.map toLegacyFrame) := by
  induction path using List.twoStepInduction generalizing t with
  | nil => rfl
  | singleton f => simp [SplayTree.splayUp, Legacy.SplayTree.splayUp, toLegacyFrame]
  | cons_cons f g path ih _ =>
    simp only [SplayTree.splayUp, List.map_cons, Legacy.SplayTree.splayUp]
    rw [ih]
    simp only [toLegacyFrame, toLegacyDir_eq_iff]
    split <;> simp_all only [toLegacy_bringUp, toLegacy_attach, toLegacy_applyChild,
      toLegacyFrame]

theorem toLegacy_descend_go [LinearOrder α] (t : BinaryTree α) (q : α)
    (acc : List (SplayTree.Frame α)) :
    Legacy.SplayTree.descend.go q (toLegacy t) (acc.map toLegacyFrame) =
      (toLegacy (SplayTree.descend.go q t acc).1,
        (SplayTree.descend.go q t acc).2.map toLegacyFrame) := by
  induction t generalizing acc with
  | nil => rfl
  | node k l r ihl ihr =>
    by_cases heq : q = k
    · simp [SplayTree.descend.go, Legacy.SplayTree.descend.go, toLegacy, heq]
    · by_cases hlt : q < k
      · simpa [SplayTree.descend.go, Legacy.SplayTree.descend.go, toLegacy,
          toLegacyFrame, toLegacyDir, heq, hlt] using
          ihl ({ dir := .L, key := k, sibling := r } :: acc)
      · simpa [SplayTree.descend.go, Legacy.SplayTree.descend.go, toLegacy,
          toLegacyFrame, toLegacyDir, heq, hlt] using
          ihr ({ dir := .R, key := k, sibling := l } :: acc)

theorem toLegacy_descend [LinearOrder α] (t : BinaryTree α) (q : α) :
    Legacy.SplayTree.descend (toLegacy t) q =
      (toLegacy (SplayTree.descend t q).1,
        (SplayTree.descend t q).2.map toLegacyFrame) :=
  toLegacy_descend_go t q []

@[simp] theorem toLegacy_splay [LinearOrder α] (t : BinaryTree α) (q : α) :
    toLegacy (SplayTree.splay t q) = Legacy.SplayTree.splay (toLegacy t) q := by
  unfold SplayTree.splay Legacy.SplayTree.splay
  rw [toLegacy_descend]
  rcases h : SplayTree.descend t q with ⟨s, path⟩
  cases s with
  | nil =>
    cases path with
    | nil => rfl
    | cons f path =>
      simpa only [toLegacy_attach, toLegacy, List.map_cons] using
        toLegacy_splayUp (f.attach .nil) path
  | node k l r => exact toLegacy_splayUp (.node k l r) path

@[simp] theorem toLegacy_splay_cost [LinearOrder α] (t : BinaryTree α) (q : α) :
    Legacy.SplayTree.splay.cost (toLegacy t) q = SplayTree.splay.cost t q := by
  unfold SplayTree.splay.cost Legacy.SplayTree.splay.cost
  rw [toLegacy_descend]
  rcases h : SplayTree.descend t q with ⟨s, path⟩
  cases s with
  | nil => cases path <;> simp [toLegacy]
  | node k l r => simp [toLegacy]

def toLegacyOp : SplayTree.DequeOp α → Legacy.SplayTree.DequeOp α
  | .pop => .pop
  | .push k => .push k
  | .eject => .eject
  | .inject k => .inject k

@[simp] theorem toLegacy_step [LinearOrder α] (t : BinaryTree α) (op : SplayTree.DequeOp α) :
    toLegacy (op.step t) = (toLegacyOp op).step (toLegacy t) := by
  cases op <;>
    simp only [toLegacyOp, SplayTree.DequeOp.step, Legacy.SplayTree.DequeOp.step,
      SplayTree.pop, SplayTree.push, SplayTree.eject, SplayTree.inject,
      Legacy.SplayTree.pop, Legacy.SplayTree.push, Legacy.SplayTree.eject,
      Legacy.SplayTree.inject, toLegacy_minKey, toLegacy_maxKey]
  · cases h : t.minKey? <;> simp only [h, toLegacy_right, toLegacy_splay] <;> rfl
  · rfl
  · cases h : t.maxKey? <;> simp only [h, toLegacy_left, toLegacy_splay] <;> rfl
  · rfl

@[simp] theorem toLegacy_valid [LinearOrder α] (t : BinaryTree α) (op : SplayTree.DequeOp α) :
    (toLegacyOp op).Valid (toLegacy t) ↔ op.Valid t := by
  cases op <;>
    simp [toLegacyOp, SplayTree.DequeOp.Valid, Legacy.SplayTree.DequeOp.Valid,
      forallTree_iff]

@[simp] theorem toLegacy_cost [LinearOrder α] (t : BinaryTree α) (op : SplayTree.DequeOp α) :
    (toLegacyOp op).cost (toLegacy t) = op.cost t := by
  cases op <;>
    simp only [toLegacyOp, SplayTree.DequeOp.cost, Legacy.SplayTree.DequeOp.cost,
      SplayTree.popCost, SplayTree.ejectCost, Legacy.SplayTree.popCost,
      Legacy.SplayTree.ejectCost, toLegacy_minKey, toLegacy_maxKey]
  · cases h : t.minKey? <;> simp [h]
  · cases h : t.maxKey? <;> simp [h]

theorem toLegacy_seq [LinearOrder α] {m : ℕ} (t : BinaryTree α)
    (ops : Fin m → SplayTree.DequeOp α) (i : Fin (m + 1)) :
    toLegacy (SplayTree.dequeSeq t ops i) =
      Legacy.SplayTree.dequeSeq (toLegacy t) (fun j => toLegacyOp (ops j)) i := by
  unfold SplayTree.dequeSeq Legacy.SplayTree.dequeSeq
  induction i.val with
  | zero => rfl
  | succ n ih =>
    dsimp only
    split <;> simp_all only [toLegacy_step]

theorem toLegacy_validSeq [LinearOrder α] {m : ℕ} (t : BinaryTree α)
    (ops : Fin m → SplayTree.DequeOp α) (h : SplayTree.ValidDequeSeq t ops) :
    Legacy.SplayTree.ValidDequeSeq (toLegacy t) (fun j => toLegacyOp (ops j)) := by
  intro i
  rw [← toLegacy_seq]
  exact (toLegacy_valid _ _).mpr (h i)

theorem toLegacy_sequenceCost [LinearOrder α] {m : ℕ} (t : BinaryTree α)
    (ops : Fin m → SplayTree.DequeOp α) :
    Legacy.SplayTree.dequeSequenceCost (toLegacy t) (fun j => toLegacyOp (ops j)) =
      SplayTree.dequeSequenceCost t ops := by
  unfold Legacy.SplayTree.dequeSequenceCost SplayTree.dequeSequenceCost
  apply Finset.sum_congr rfl
  intro i hi
  rw [← toLegacy_seq, toLegacy_cost]

theorem ackermann_eq (i j : ℕ) : Legacy.SplayTree.ackermann i j = SplayTree.ackermann i j := by
  have step : ∀ (f : ℕ → ℕ) (n : ℕ),
      Legacy.SplayTree.ackermannStep f n = SplayTree.ackermannStep f n := by
    intro f n
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => rfl
    | more n _ ih => simpa [Legacy.SplayTree.ackermannStep, SplayTree.ackermannStep] using congrArg f ih
  induction i using Nat.twoStepInduction generalizing j with
  | zero => rfl
  | one => rfl
  | more i _ ih =>
    simp only [Legacy.SplayTree.ackermann, SplayTree.ackermann, step]
    rw [show Legacy.SplayTree.ackermann (i + 1) = SplayTree.ackermann (i + 1) from funext ih]

theorem invAckermann_eq : Legacy.SplayTree.invAckermann = SplayTree.invAckermann := by
  funext n
  simp only [Legacy.SplayTree.invAckermann, SplayTree.invAckermann, ackermann_eq]

theorem hierarchy_eq (r : ℕ) :
    Legacy.SplayTree.iteratedInvAckermannHierarchy r = SplayTree.iteratedInvAckermannHierarchy r := by
  induction r with
  | zero => exact invAckermann_eq
  | succ r ih =>
    simp only [Legacy.SplayTree.iteratedInvAckermannHierarchy,
      SplayTree.iteratedInvAckermannHierarchy, ih]

theorem ordinalOmegaInvAckermann_eq (n : ℕ) :
    Legacy.SplayTree.ordinalOmegaInvAckermann n = SplayTree.ordinalOmegaInvAckermann n := by
  simp only [Legacy.SplayTree.ordinalOmegaInvAckermann, SplayTree.ordinalOmegaInvAckermann,
    hierarchy_eq]

end SplayDeque.Bridge
