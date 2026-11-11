module

public import Challenge.Definitions
public import Solution.TreeFacts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

@[expose] public section

namespace Solution.KeyAssignmentSpine

open SplayTree BinaryTree

/-! ## Section 1: Basic `BinaryTree`, `keyFinset`, `pop`, and `eject` Lemmas -/

private theorem map_num_nodes {α β : Type} (f : α → β) (t : BinaryTree α) :
    (t.map f).num_nodes = t.num_nodes := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr => simp [BinaryTree.map, num_nodes, ihl, ihr]

private theorem toKeyList_map {α β : Type} (f : α → β) (t : BinaryTree α) :
    (t.map f).toKeyList = t.toKeyList.map f := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr => simp [BinaryTree.map, toKeyList, ihl, ihr]

private theorem mem_map_iff {α β : Type} (f : α → β) (t : BinaryTree α) (y : β) :
    y ∈ t.map f ↔ ∃ x ∈ t, f x = y := by
  rw [mem_iff_mem_toKeyList, toKeyList_map, List.mem_map]
  simp only [mem_iff_mem_toKeyList]

private theorem mirror_map {α β : Type} (f : α → β) (t : BinaryTree α) :
    (t.map f).mirror = t.mirror.map f := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr => simp [BinaryTree.map, mirror, ihl, ihr]

private theorem mem_mirror_iff {α : Type} (t : BinaryTree α) (x : α) :
    x ∈ t.mirror ↔ x ∈ t := by
  rw [mem_iff_mem_toKeyList, toKeyList_mirror, List.mem_reverse, ← mem_iff_mem_toKeyList]

private theorem mem_keyFinset_iff {α : Type} [DecidableEq α] (t : BinaryTree α) (x : α) :
    x ∈ keyFinset t ↔ x ∈ t := by
  induction t with
  | nil => simp [keyFinset]
  | node k l r ihl ihr =>
    simp only [keyFinset, Finset.mem_insert, Finset.mem_union, mem_node_iff, ihl, ihr]

private theorem toKeyList_toFinset_eq {α : Type} [DecidableEq α] (t : BinaryTree α) :
    t.toKeyList.toFinset = keyFinset t := by
  ext x
  rw [List.mem_toFinset, ← mem_iff_mem_toKeyList, mem_keyFinset_iff]

private theorem card_keyFinset_of_isBST {α : Type} [LinearOrder α] (t : BinaryTree α)
    (ht : t.IsBST) :
    (open Classical in (keyFinset t).card) = t.num_nodes := by
  classical
  have hsorted : t.toKeyList.Pairwise (· < ·) := (IsBST_iff_toKeyList_sorted t).mp ht
  have hnodup : t.toKeyList.Nodup := hsorted.imp ne_of_lt
  rw [← toKeyList_toFinset_eq, List.toFinset_card_of_nodup hnodup, num_nodes_eq_length_toKeyList]

private theorem minKey?_eq_none_iff {α : Type} (t : BinaryTree α) :
    t.minKey? = none ↔ t = .nil := by
  cases t with
  | nil => simp [BinaryTree.minKey?]
  | node k l r =>
    simp only [BinaryTree.minKey?, reduceCtorEq, iff_false]
    cases l.minKey? <;> simp

private theorem maxKey?_eq_none_iff {α : Type} (t : BinaryTree α) :
    t.maxKey? = none ↔ t = .nil := by
  cases t with
  | nil => simp [BinaryTree.maxKey?]
  | node k l r =>
    simp only [BinaryTree.maxKey?, reduceCtorEq, iff_false]
    cases r.maxKey? <;> simp

private theorem minKey?_mem {α : Type} (t : BinaryTree α) (x : α) (h : t.minKey? = some x) :
    x ∈ t := by
  induction t generalizing x with
  | nil => simp [BinaryTree.minKey?] at h
  | node k l r ihl _ =>
    simp only [BinaryTree.minKey?] at h
    cases hl : l.minKey? with
    | none =>
      rw [hl] at h; injection h with hEq; subst hEq; exact .here
    | some m =>
      rw [hl] at h; injection h with hEq; subst hEq; exact .left (ihl m hl)

private theorem minKey?_le_of_isBST {α : Type} [LinearOrder α] (t : BinaryTree α) (x : α)
    (ht : t.IsBST) (hmin : t.minKey? = some x) : ∀ y ∈ t, x ≤ y := by
  induction t generalizing x with
  | nil => simp [BinaryTree.minKey?] at hmin
  | node k l r ihl _ =>
    simp only [BinaryTree.minKey?] at hmin
    have hl_bst := IsBST_left_of_IsBST ht
    cases hl : l.minKey? with
    | none =>
      rw [hl] at hmin
      rcases Option.some.inj hmin with rfl
      have hl_nil : l = .nil := (minKey?_eq_none_iff l).mp hl
      subst hl_nil
      intro y hy
      rcases mem_node_iff.mp hy with rfl | hyl | hyr
      · exact le_rfl
      · simp at hyl
      · exact le_of_lt (gt_of_IsBST_right .nil k r ht hyr)
    | some m =>
      rw [hl] at hmin
      rcases Option.some.inj hmin with rfl
      have hm_lt_k : m < k := lt_of_IsBST_left l k r ht (minKey?_mem l m hl)
      intro y hy
      rcases mem_node_iff.mp hy with rfl | hyl | hyr
      · exact le_of_lt hm_lt_k
      · exact ihl m hl_bst hl y hyl
      · exact le_of_lt (lt_trans hm_lt_k (gt_of_IsBST_right l k r ht hyr))

/-! ### Unlabeled and Polymorphic Left-Spine Splay (`pop` and `OrderDual` `eject`) -/

private def leftSpineLenU : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ l _ => 1 + leftSpineLenU l

private def rightSpineLenU : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ _ r => 1 + rightSpineLenU r

private def descendLeftPoly {α : Type} :
    BinaryTree α → List (α × BinaryTree α) → BinaryTree α × List (α × BinaryTree α)
  | .nil, acc => (.nil, acc)
  | .node _ .nil r, acc => (r, acc)
  | .node k l@(.node _ _ _) r, acc => descendLeftPoly l ((k, r) :: acc)

private def splayLeftSpinePoly {α : Type} :
    BinaryTree α → List (α × BinaryTree α) → BinaryTree α
  | c, [] => c
  | c, [(k1, s1)] => .node k1 c s1
  | c, (k1, s1) :: (k2, s2) :: rest =>
      splayLeftSpinePoly (.node k1 c (.node k2 s1 s2)) rest

private def popPoly {α : Type} (t : BinaryTree α) : BinaryTree α :=
  let (c, path) := descendLeftPoly t []
  splayLeftSpinePoly c path

private def toFrameL {α : Type} (p : α × BinaryTree α) : Frame α :=
  { dir := .L, key := p.1, sibling := p.2 }

private theorem descendLeftPoly_map {α β : Type} (f : α → β) (t : BinaryTree α)
    (acc : List (α × BinaryTree α)) :
    descendLeftPoly (t.map f) (acc.map (fun p => (f p.1, p.2.map f))) =
      ((descendLeftPoly t acc).1.map f,
       (descendLeftPoly t acc).2.map (fun p => (f p.1, p.2.map f))) := by
  induction t generalizing acc with
  | nil => simp [descendLeftPoly, BinaryTree.map]
  | node k l r ihl _ =>
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp [descendLeftPoly, BinaryTree.map]
    · simpa [BinaryTree.map, descendLeftPoly] using ihl ((k, r) :: acc)

private theorem splayLeftSpinePoly_map {α β : Type} (f : α → β) (c : BinaryTree α)
    (path : List (α × BinaryTree α)) :
    (splayLeftSpinePoly c path).map f =
      splayLeftSpinePoly (c.map f) (path.map (fun p => (f p.1, p.2.map f))) := by
  induction path using List.twoStepInduction generalizing c with
  | nil => rfl
  | singleton p => rcases p with ⟨k1, s1⟩; rfl
  | cons_cons p1 p2 rest ih _ =>
    rcases p1 with ⟨k1, s1⟩; rcases p2 with ⟨k2, s2⟩
    simpa [splayLeftSpinePoly, BinaryTree.map] using ih (.node k1 c (.node k2 s1 s2))

private theorem popPoly_map {α β : Type} (f : α → β) (t : BinaryTree α) :
    (popPoly t).map f = popPoly (t.map f) := by
  unfold popPoly
  have hd := descendLeftPoly_map f t []
  simp only [List.map_nil] at hd
  rw [hd, splayLeftSpinePoly_map]

private theorem descendLeftPoly_len {α : Type} (t : BinaryTree α)
    (acc : List (α × BinaryTree α)) (hne : t ≠ .nil) :
    (descendLeftPoly t acc).2.length + 1 = leftSpineLenU (t.map (fun _ => ())) + acc.length := by
  induction t generalizing acc with
  | nil => exact absurd rfl hne
  | node k l r ihl _ =>
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp [descendLeftPoly, BinaryTree.map, leftSpineLenU]; omega
    · have h1 := ihl ((k, r) :: acc) (by simp)
      simp only [descendLeftPoly, List.length_cons, BinaryTree.map, leftSpineLenU] at h1 ⊢
      omega

private theorem descend_go_minKey {α : Type} [LinearOrder α] (t : BinaryTree α) (x : α)
    (acc : List (α × BinaryTree α)) (ht : t.IsBST) (hmin : t.minKey? = some x) :
    descend.go x t (acc.map toFrameL) =
      (.node x .nil (descendLeftPoly t acc).1, (descendLeftPoly t acc).2.map toFrameL) := by
  induction t generalizing acc with
  | nil => simp [BinaryTree.minKey?] at hmin
  | node k l r ihl _ =>
    have hl_bst := IsBST_left_of_IsBST ht
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp only [BinaryTree.minKey?, Option.some.injEq] at hmin
      subst hmin
      simp [descend.go, descendLeftPoly]
    · have hl_ne : BinaryTree.node lk ll lr ≠ .nil := by simp
      cases hl : (BinaryTree.node lk ll lr).minKey? with
      | none => exact absurd ((minKey?_eq_none_iff _).mp hl) hl_ne
      | some m =>
        have hnode_min : (BinaryTree.node k (BinaryTree.node lk ll lr) r).minKey? =
            match (BinaryTree.node lk ll lr).minKey? with
            | none => some k
            | some m => some m := rfl
        rw [hnode_min, hl] at hmin
        rcases Option.some.inj hmin with rfl
        have hm_lt : m < k := lt_of_IsBST_left _ k r ht (minKey?_mem _ m hl)
        have hm_ne : m ≠ k := ne_of_lt hm_lt
        simp only [descend.go, hm_ne, hm_lt, ↓reduceIte, descendLeftPoly]
        exact ihl ((k, r) :: acc) hl_bst hl

private theorem splayUp_toFrameL {α : Type} (x : α) (c : BinaryTree α)
    (path : List (α × BinaryTree α)) :
    splayUp (.node x .nil c) (path.map toFrameL) =
      .node x .nil (splayLeftSpinePoly c path) := by
  induction path using List.twoStepInduction generalizing c with
  | nil => rfl
  | singleton p => rcases p with ⟨k1, s1⟩; rfl
  | cons_cons p1 p2 rest ih _ =>
    rcases p1 with ⟨k1, s1⟩; rcases p2 with ⟨k2, s2⟩
    simpa [splayUp, toFrameL, Frame.attach, Dir.bringUp, BinaryTree.rotateRight,
      splayLeftSpinePoly] using ih (.node k1 c (.node k2 s1 s2))

private theorem pop_spec_poly {α : Type} [LinearOrder α] (t : BinaryTree α)
    (ht : t.IsBST) (hne : t ≠ .nil) :
    ∃ x : α,
      t.minKey? = some x ∧
      x ∈ t ∧
      (∀ y ∈ t, x ≤ y) ∧
      SplayTree.pop t = popPoly t ∧
      popCost t = ((leftSpineLenU (t.map (fun _ => ())) - 1 : ℕ) : ℝ) ∧
      t.toKeyList = x :: (SplayTree.pop t).toKeyList ∧
      (SplayTree.pop t).IsBST ∧
      (∀ y ∈ SplayTree.pop t, x < y) ∧
      (SplayTree.pop t).num_nodes + 1 = t.num_nodes := by
  cases hmin : t.minKey? with
  | none => exact absurd ((minKey?_eq_none_iff t).mp hmin) hne
  | some x =>
    have hd := descend_go_minKey t x [] ht hmin
    simp only [List.map_nil] at hd
    have hsplay : splay t x = .node x .nil (popPoly t) := by
      unfold splay descend popPoly
      rw [hd]
      exact splayUp_toFrameL x _ _
    have hpop_eq : SplayTree.pop t = popPoly t := by
      unfold SplayTree.pop
      rw [hmin]
      dsimp only
      rw [hsplay]
      rfl
    have hcost_eq : popCost t = ((leftSpineLenU (t.map (fun _ => ())) - 1 : ℕ) : ℝ) := by
      have hlen := descendLeftPoly_len t [] hne
      simp only [List.length_nil, Nat.add_zero] at hlen
      unfold popCost
      rw [hmin]
      dsimp only
      unfold splay.cost descend
      rw [hd]
      dsimp only
      rw [List.length_map]
      have : (descendLeftPoly t []).2.length = leftSpineLenU (t.map (fun _ => ())) - 1 := by omega
      rw [this]
    have hkeys : t.toKeyList = x :: (SplayTree.pop t).toKeyList := by
      have hk := toKeyList_splay t x
      rw [hsplay, ← hpop_eq] at hk
      simpa [toKeyList] using hk.symm
    have hsorted : (x :: (SplayTree.pop t).toKeyList).Pairwise (· < ·) := by
      rw [← hkeys]
      exact (IsBST_iff_toKeyList_sorted t).mp ht
    rw [List.pairwise_cons] at hsorted
    have hpop_bst : (SplayTree.pop t).IsBST :=
      (IsBST_iff_toKeyList_sorted _).mpr hsorted.2
    have hpop_gt : ∀ y ∈ SplayTree.pop t, x < y := by
      intro y hy
      exact hsorted.1 y (mem_iff_mem_toKeyList.mp hy)
    have hnodes : (SplayTree.pop t).num_nodes + 1 = t.num_nodes := by
      rw [num_nodes_eq_length_toKeyList, num_nodes_eq_length_toKeyList t, hkeys, List.length_cons]
    exact ⟨x, rfl, minKey?_mem t x hmin, minKey?_le_of_isBST t x ht hmin,
      hpop_eq, hcost_eq, hkeys, hpop_bst, hpop_gt, hnodes⟩

/-! ### Order-Dual Mirror for `eject` on Arbitrary `[LinearOrder α]` -/

private def dualTree {α : Type} (t : BinaryTree α) : BinaryTree αᵒᵈ :=
  (t.map OrderDual.toDual).mirror

private def dualFrame {α : Type} (f : Frame α) : Frame αᵒᵈ :=
  { dir := f.dir.flip, key := OrderDual.toDual f.key, sibling := dualTree f.sibling }

private theorem map_map {α β γ : Type} (f : α → β) (g : β → γ) (t : BinaryTree α) :
    (t.map f).map g = t.map (g ∘ f) := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr => simp [BinaryTree.map, ihl, ihr]

private theorem map_id' {α : Type} (t : BinaryTree α) : t.map (fun x => x) = t := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr => simp [BinaryTree.map, ihl, ihr]

private theorem unDual_dualTree {α : Type} (t : BinaryTree α) :
    (dualTree t).mirror.map OrderDual.ofDual = t := by
  rw [dualTree, mirror_mirror, map_map]
  exact map_id' t

private theorem dualTree_isBST {α : Type} [LinearOrder α] (t : BinaryTree α) (ht : t.IsBST) :
    (dualTree t).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at ht ⊢
  unfold dualTree
  rw [toKeyList_mirror, toKeyList_map, List.pairwise_reverse]
  rw [List.pairwise_map]
  exact ht.imp (fun {a b} hab => OrderDual.toDual_lt_toDual.mpr hab)

private theorem dualTree_minKey? {α : Type} (t : BinaryTree α) :
    (dualTree t).minKey? = t.maxKey?.map OrderDual.toDual := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    simp only [dualTree, BinaryTree.map, mirror, BinaryTree.minKey?, BinaryTree.maxKey?]
    change (match (dualTree r).minKey? with
      | none => some (OrderDual.toDual k) | some m => some m) = _
    rw [ihr]
    cases r.maxKey? <;> rfl

private theorem descend_go_dualTree {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α)
    (acc : List (Frame α)) :
    descend.go (OrderDual.toDual q) (dualTree t) (acc.map dualFrame) =
      (dualTree (descend.go q t acc).1, (descend.go q t acc).2.map dualFrame) := by
  induction t generalizing acc with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [dualTree, BinaryTree.map, mirror, descend.go]
    by_cases hqk : q = k
    · subst hqk
      simp [BinaryTree.map]
    · have hnq : OrderDual.toDual q ≠ OrderDual.toDual k :=
        fun h => hqk (OrderDual.toDual.injective h)
      by_cases hqlt : q < k
      · have hnot : ¬(OrderDual.toDual q < OrderDual.toDual k) :=
          not_lt.mpr (OrderDual.toDual_le_toDual.mpr (le_of_lt hqlt))
        simp only [hqk, hqlt, hnq, hnot, ↓reduceIte]
        exact ihl ({ dir := .L, key := k, sibling := r } :: acc)
      · have hklt : k < q := lt_of_le_of_ne (not_lt.mp hqlt) (Ne.symm hqk)
        have hyes : OrderDual.toDual q < OrderDual.toDual k :=
          OrderDual.toDual_lt_toDual.mpr hklt
        simp only [hqk, hqlt, hnq, hyes, ↓reduceIte]
        exact ihr ({ dir := .R, key := k, sibling := l } :: acc)

private theorem dualTree_bringUp {α : Type} (d : Dir) (t : BinaryTree α) :
    dualTree (d.bringUp t) = d.flip.bringUp (dualTree t) := by
  cases d <;> rcases t with _ | ⟨k, _ | ⟨lk, ll, lr⟩, _ | ⟨rk, rl, rr⟩⟩ <;> rfl

private theorem dualTree_attach {α : Type} (c : BinaryTree α) (f : Frame α) :
    dualTree (f.attach c) = (dualFrame f).attach (dualTree c) := by
  rcases f with ⟨_ | _, k, sib⟩ <;> rfl

private theorem dualTree_applyChild_bringUp {α : Type} (d1 d2 : Dir) (t : BinaryTree α) :
    dualTree (applyChild d2 d1.bringUp t) =
      applyChild d2.flip d1.flip.bringUp (dualTree t) := by
  rcases t with _ | ⟨k, l, r⟩
  · cases d1 <;> cases d2 <;> rfl
  · cases d2
    · change dualTree ((d1.bringUp l) △[k] r) = applyChild .R d1.flip.bringUp (dualTree (l △[k] r))
      have h := dualTree_bringUp d1 l
      simp only [applyChild, dualTree, BinaryTree.map, mirror] at h ⊢
      rw [h]
    · change dualTree (l △[k] (d1.bringUp r)) = applyChild .L d1.flip.bringUp (dualTree (l △[k] r))
      have h := dualTree_bringUp d1 r
      simp only [applyChild, dualTree, BinaryTree.map, mirror] at h ⊢
      rw [h]

private theorem dualTree_splayUp {α : Type} (c : BinaryTree α) (path : List (Frame α)) :
    dualTree (splayUp c path) = splayUp (dualTree c) (path.map dualFrame) := by
  induction path using List.twoStepInduction generalizing c with
  | nil => rfl
  | singleton f =>
    simp [splayUp, dualTree_bringUp, dualTree_attach, dualFrame]
  | cons_cons f1 f2 rest ih _ =>
    have hflip_iff : f1.dir.flip = f2.dir.flip ↔ f1.dir = f2.dir := by
      cases f1.dir <;> cases f2.dir <;> decide
    simp only [List.map_cons, splayUp]
    by_cases hd : f1.dir = f2.dir
    · have hdf : (dualFrame f1).dir = (dualFrame f2).dir := hflip_iff.mpr hd
      simp only [hd, hdf, ↓reduceIte]
      rw [ih, dualTree_bringUp, dualTree_bringUp, dualTree_attach, dualTree_attach]
      rfl
    · have hdf : (dualFrame f1).dir ≠ (dualFrame f2).dir := mt hflip_iff.mp hd
      simp only [hd, hdf, ↓reduceIte]
      rw [ih, dualTree_bringUp, dualTree_applyChild_bringUp, dualTree_attach, dualTree_attach]
      rfl

private theorem dualTree_splay {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α) :
    dualTree (splay t q) = splay (dualTree t) (OrderDual.toDual q) := by
  unfold splay descend
  have hd := descend_go_dualTree t q []
  simp only [List.map_nil] at hd
  rw [hd]
  rcases hdg : descend.go q t [] with ⟨c, path⟩
  cases c with
  | nil =>
    cases path with
    | nil => rfl
    | cons f rest =>
      change dualTree (splayUp (f.attach .nil) rest) =
        splayUp ((dualFrame f).attach .nil) (rest.map dualFrame)
      rw [dualTree_splayUp, dualTree_attach]
      rfl
  | node ck cl cr =>
    exact dualTree_splayUp (.node ck cl cr) path

private theorem splay_cost_dualTree {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α) :
    splay.cost t q = splay.cost (dualTree t) (OrderDual.toDual q) := by
  unfold splay.cost descend
  have hd := descend_go_dualTree t q []
  simp only [List.map_nil] at hd
  rw [hd]
  rcases descend.go q t [] with ⟨_ | ⟨ck, cl, cr⟩, _ | ⟨f, rest⟩⟩ <;>
    simp [dualTree, BinaryTree.map]

private def ejectPoly {α : Type} (t : BinaryTree α) : BinaryTree α :=
  (popPoly t.mirror).mirror

private theorem leftSpineLenU_mirror (u : BinaryTree Unit) :
    leftSpineLenU u.mirror = rightSpineLenU u := by
  induction u with
  | nil => rfl
  | node _ l r _ ihr => simp [mirror, leftSpineLenU, rightSpineLenU, ihr]

private theorem eject_spec_poly {α : Type} [LinearOrder α] (t : BinaryTree α)
    (ht : t.IsBST) (hne : t ≠ .nil) :
    ∃ z : α,
      t.maxKey? = some z ∧
      z ∈ t ∧
      (∀ y ∈ t, y ≤ z) ∧
      SplayTree.eject t = ejectPoly t ∧
      ejectCost t = ((rightSpineLenU (t.map (fun _ => ())) - 1 : ℕ) : ℝ) ∧
      t.toKeyList = (SplayTree.eject t).toKeyList ++ [z] ∧
      (SplayTree.eject t).IsBST ∧
      (∀ y ∈ SplayTree.eject t, y < z) ∧
      (SplayTree.eject t).num_nodes + 1 = t.num_nodes := by
  have hd_ne : dualTree t ≠ .nil := by
    rcases t with _ | ⟨k, l, r⟩
    · exact absurd rfl hne
    · simp [dualTree, BinaryTree.map]
  obtain ⟨nx, hnmin, _, _, hnpop, hncost, hnkeys, _, _, _⟩ :=
    pop_spec_poly (dualTree t) (dualTree_isBST t ht) hd_ne
  rw [dualTree_minKey?] at hnmin
  cases hmax : t.maxKey? with
  | none => simp [hmax] at hnmin
  | some z =>
    simp only [hmax, Option.map_some, Option.some.injEq] at hnmin
    subst hnmin
    have hright_dual : ∀ u : BinaryTree α, (dualTree u).right = dualTree u.left := by
      rintro (_ | ⟨k, l, r⟩) <;> rfl
    have hej_dual : dualTree (SplayTree.eject t) = SplayTree.pop (dualTree t) := by
      unfold SplayTree.eject SplayTree.pop
      rw [hmax, dualTree_minKey?, hmax]
      dsimp only [Option.map_some]
      rw [← hright_dual, dualTree_splay]
    have hpop_dual_eq : popPoly (dualTree t) = dualTree (ejectPoly t) := by
      unfold dualTree ejectPoly
      rw [mirror_map, ← popPoly_map, mirror_map, mirror_mirror]
    have hej_eq : SplayTree.eject t = ejectPoly t := by
      have h1 : dualTree (SplayTree.eject t) = dualTree (ejectPoly t) := by
        rw [hej_dual, hnpop, hpop_dual_eq]
      have h2 := congrArg (fun u => u.mirror.map OrderDual.ofDual) h1
      simpa only [unDual_dualTree] using h2
    have hcost_eq : ejectCost t = ((rightSpineLenU (t.map (fun _ => ())) - 1 : ℕ) : ℝ) := by
      unfold ejectCost
      rw [hmax]
      dsimp only
      rw [splay_cost_dualTree]
      have hpop_cost_d : popCost (dualTree t) = splay.cost (dualTree t) (OrderDual.toDual z) := by
        unfold popCost
        rw [dualTree_minKey?, hmax]
        rfl
      rw [← hpop_cost_d, hncost]
      have hmap_eq : (dualTree t).map (fun _ => ()) = (t.map (fun _ => ())).mirror := by
        rw [dualTree, ← mirror_map, map_map]
      rw [hmap_eq, leftSpineLenU_mirror]
    have hkeys_eq : t.toKeyList = (SplayTree.eject t).toKeyList ++ [z] := by
      rw [← hej_dual] at hnkeys
      unfold dualTree at hnkeys
      rw [toKeyList_mirror, toKeyList_map, toKeyList_mirror, toKeyList_map] at hnkeys
      have hrev := congrArg (fun xs => xs.reverse.map OrderDual.ofDual) hnkeys
      simpa [List.map_reverse, List.map_append, Function.comp_def] using hrev
    have hsorted : ((SplayTree.eject t).toKeyList ++ [z]).Pairwise (· < ·) := by
      rw [← hkeys_eq]
      exact (IsBST_iff_toKeyList_sorted t).mp ht
    rw [List.pairwise_append] at hsorted
    have hej_bst : (SplayTree.eject t).IsBST :=
      (IsBST_iff_toKeyList_sorted _).mpr hsorted.1
    have hej_lt : ∀ y ∈ SplayTree.eject t, y < z := by
      intro y hy
      exact hsorted.2.2 y (mem_iff_mem_toKeyList.mp hy) z (List.mem_singleton_self z)
    have hz_mem : z ∈ t := by
      rw [mem_iff_mem_toKeyList, hkeys_eq]
      simp
    have hz_ge : ∀ y ∈ t, y ≤ z := by
      intro y hy
      rw [mem_iff_mem_toKeyList, hkeys_eq, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy' | rfl
      · exact le_of_lt (hej_lt y (mem_iff_mem_toKeyList.mpr hy'))
      · exact le_rfl
    have hnodes : (SplayTree.eject t).num_nodes + 1 = t.num_nodes := by
      rw [num_nodes_eq_length_toKeyList, num_nodes_eq_length_toKeyList t, hkeys_eq,
        List.length_append, List.length_singleton]
    exact ⟨z, rfl, hz_mem, hz_ge, hej_eq, hcost_eq, hkeys_eq, hej_bst, hej_lt, hnodes⟩

private theorem ejectPoly_map {α β : Type} (f : α → β) (t : BinaryTree α) :
    (ejectPoly t).map f = ejectPoly (t.map f) := by
  unfold ejectPoly
  rw [← mirror_map, popPoly_map, mirror_map]

/-! ## Section 2: Offline Nested-Interval Three-Way Key Assignment (Lemma 3.3) -/

private theorem isBST_push {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α)
    (ht : t.IsBST) (hq : ∀ y ∈ t, q < y) : (SplayTree.push t q).IsBST :=
  SplayDeque.Direct.isBSTNode q .nil t .left
    ((SplayDeque.Direct.forallTree_iff _ _).mpr hq) SplayDeque.Direct.isBSTNil ht

private theorem isBST_inject {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α)
    (ht : t.IsBST) (hq : ∀ y ∈ t, y < q) : (SplayTree.inject t q).IsBST :=
  SplayDeque.Direct.isBSTNode q t .nil
    ((SplayDeque.Direct.forallTree_iff _ _).mpr hq) .left ht SplayDeque.Direct.isBSTNil

private theorem dequeSeq_zero {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin m → DequeOp α) :
    dequeSeq init ops 0 = init := rfl

private theorem dequeSeq_step {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin m → DequeOp α) (i : Fin m) :
    dequeSeq init ops i.succ = (ops i).step (dequeSeq init ops i.castSucc) := by
  unfold dequeSeq
  simp [Fin.val_succ, i.isLt]

private theorem dequeSeq_succ_cons {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin (m + 1) → DequeOp α) (t : Fin (m + 1)) :
    dequeSeq init ops t.succ = dequeSeq ((ops 0).step init) (fun j => ops j.succ) t := by
  induction t using Fin.induction with
  | zero => exact dequeSeq_step init ops 0
  | succ k ih =>
    rw [dequeSeq_step init ops k.succ, dequeSeq_step _ _ k]
    have hcs : k.succ.castSucc = k.castSucc.succ := rfl
    rw [hcs, ih]

private theorem validDequeSeq_cons_iff {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin (m + 1) → DequeOp α) :
    ValidDequeSeq init ops ↔
      (ops 0).Valid init ∧ ValidDequeSeq ((ops 0).step init) (fun j => ops j.succ) := by
  unfold ValidDequeSeq
  rw [Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨h0, fun j => ?_⟩
    have hj := hs j
    have hcs : j.succ.castSucc = j.castSucc.succ := rfl
    rw [hcs, dequeSeq_succ_cons] at hj
    exact hj
  · rintro ⟨h0, hs⟩
    refine ⟨h0, fun j => ?_⟩
    have hcs : j.succ.castSucc = j.castSucc.succ := rfl
    rw [hcs, dequeSeq_succ_cons]
    exact hs j

private theorem dequeSequenceCost_cons {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin (m + 1) → DequeOp α) :
    dequeSequenceCost init ops =
      (ops 0).cost init + dequeSequenceCost ((ops 0).step init) (fun j => ops j.succ) := by
  unfold dequeSequenceCost
  rw [Fin.sum_univ_succ]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcs : j.succ.castSucc = j.castSucc.succ := rfl
  rw [hcs, dequeSeq_succ_cons]

private theorem popCount_cons {α : Type} {m : ℕ} (ops : Fin (m + 1) → DequeOp α) :
    popCount ops = (if (ops 0).isPop then 1 else 0) + popCount (fun j => ops j.succ) := by
  simp only [popCount, Finset.card_filter]
  exact Fin.sum_univ_succ _

private theorem ejectCount_cons {α : Type} {m : ℕ} (ops : Fin (m + 1) → DequeOp α) :
    ejectCount ops = (if (ops 0).isEject then 1 else 0) + ejectCount (fun j => ops j.succ) := by
  simp only [ejectCount, Finset.card_filter]
  exact Fin.sum_univ_succ _

private theorem popDeletedKeys_cons {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin (m + 1) → DequeOp α) :
    popDeletedKeys init ops =
      (match if (ops 0).isPop then init.minKey? else none with
       | none => []
       | some x => [x]) ++
        popDeletedKeys ((ops 0).step init) (fun j => ops j.succ) := by
  unfold popDeletedKeys
  rw [List.finRange_succ, List.filterMap_cons, List.filterMap_map]
  have htail :
      ((fun i : Fin (m + 1) =>
          if (ops i).isPop then (dequeSeq init ops i.castSucc).minKey? else none) ∘ Fin.succ) =
        fun j : Fin m =>
          if (ops j.succ).isPop then
            (dequeSeq ((ops 0).step init) (fun k => ops k.succ) j.castSucc).minKey?
          else none := by
    funext j
    simp only [Function.comp_apply]
    have hcs : j.succ.castSucc = j.castSucc.succ := rfl
    rw [hcs, dequeSeq_succ_cons]
  rw [htail]
  have h0 : dequeSeq init ops (0 : Fin (m + 1)).castSucc = init := rfl
  rw [h0]
  cases (if (ops 0).isPop then init.minKey? else none) <;> rfl

private theorem ejectDeletedKeys_cons {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin (m + 1) → DequeOp α) :
    ejectDeletedKeys init ops =
      (match if (ops 0).isEject then init.maxKey? else none with
       | none => []
       | some z => [z]) ++
        ejectDeletedKeys ((ops 0).step init) (fun j => ops j.succ) := by
  unfold ejectDeletedKeys
  rw [List.finRange_succ, List.filterMap_cons, List.filterMap_map]
  have htail :
      ((fun i : Fin (m + 1) =>
          if (ops i).isEject then (dequeSeq init ops i.castSucc).maxKey? else none) ∘ Fin.succ) =
        fun j : Fin m =>
          if (ops j.succ).isEject then
            (dequeSeq ((ops 0).step init) (fun k => ops k.succ) j.castSucc).maxKey?
          else none := by
    funext j
    simp only [Function.comp_apply]
    have hcs : j.succ.castSucc = j.castSucc.succ := rfl
    rw [hcs, dequeSeq_succ_cons]
  rw [htail]
  have h0 : dequeSeq init ops (0 : Fin (m + 1)).castSucc = init := rfl
  rw [h0]
  cases (if (ops 0).isEject then init.maxKey? else none) <;> rfl

private noncomputable def opInsSet : DequeOp ℝ → Finset ℝ
  | .push x => {x}
  | .inject x => {x}
  | _ => ∅

private noncomputable def everKeys {m : ℕ} (T0 : BinaryTree ℝ) (opsR : Fin m → DequeOp ℝ) :
    Finset ℝ :=
  open Classical in
  keyFinset T0 ∪ Finset.univ.biUnion (fun i : Fin m =>
    match opsR i with
    | .push x => {x}
    | .inject x => {x}
    | _ => ∅)

private theorem everKeys_eq_biUnion {m : ℕ} (T0 : BinaryTree ℝ) (opsR' : Fin m → DequeOp ℝ) :
    everKeys T0 opsR' =
      (open Classical in keyFinset T0) ∪
        Finset.univ.biUnion (fun j : Fin m => opInsSet (opsR' j)) := rfl

private theorem everKeys_cons {m : ℕ} (T0 : BinaryTree ℝ) (op0 : DequeOp ℝ)
    (opsR' : Fin m → DequeOp ℝ) :
    everKeys T0 (Fin.cons op0 opsR') =
      (open Classical in keyFinset T0) ∪ opInsSet op0 ∪
        Finset.univ.biUnion (fun j : Fin m => opInsSet (opsR' j)) := by
  classical
  rw [everKeys_eq_biUnion]
  ext x
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro (hx | ⟨i, hi⟩)
    · exact Or.inl (Or.inl hx)
    · refine Fin.cases ?_ ?_ i hi
      · intro h0
        exact Or.inl (Or.inr h0)
      · intro j hj
        exact Or.inr ⟨j, hj⟩
  · rintro ((hx | h0) | ⟨j, hj⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨0, h0⟩
    · exact Or.inr ⟨j.succ, hj⟩

private theorem everKeys_cons_push {m : ℕ} (T0 : BinaryTree ℝ) (q : ℝ)
    (opsR' : Fin m → DequeOp ℝ) :
    everKeys T0 (Fin.cons (.push q) opsR') = everKeys (SplayTree.push T0 q) opsR' := by
  classical
  rw [everKeys_cons, everKeys_eq_biUnion]
  ext x
  simp [SplayTree.push, keyFinset, opInsSet]

private theorem everKeys_cons_inject {m : ℕ} (T0 : BinaryTree ℝ) (q : ℝ)
    (opsR' : Fin m → DequeOp ℝ) :
    everKeys T0 (Fin.cons (.inject q) opsR') = everKeys (SplayTree.inject T0 q) opsR' := by
  classical
  rw [everKeys_cons, everKeys_eq_biUnion]
  ext x
  simp [SplayTree.inject, keyFinset, opInsSet]

private theorem everKeys_cons_pop {m : ℕ} (T0 : BinaryTree ℝ) (x : ℝ)
    (opsR' : Fin m → DequeOp ℝ)
    (hkeys : T0.toKeyList = x :: (SplayTree.pop T0).toKeyList) :
    everKeys T0 (Fin.cons .pop opsR') = insert x (everKeys (SplayTree.pop T0) opsR') := by
  classical
  have hkf : keyFinset T0 = insert x (keyFinset (SplayTree.pop T0)) := by
    ext y
    simp only [mem_keyFinset_iff, mem_iff_mem_toKeyList, hkeys, List.mem_cons, Finset.mem_insert]
  rw [everKeys_cons, everKeys_eq_biUnion, hkf]
  ext y
  simp [opInsSet]

private theorem everKeys_cons_eject {m : ℕ} (T0 : BinaryTree ℝ) (z : ℝ)
    (opsR' : Fin m → DequeOp ℝ)
    (hkeys : T0.toKeyList = (SplayTree.eject T0).toKeyList ++ [z]) :
    everKeys T0 (Fin.cons .eject opsR') = insert z (everKeys (SplayTree.eject T0) opsR') := by
  classical
  have hkf : keyFinset T0 = insert z (keyFinset (SplayTree.eject T0)) := by
    ext y
    simp only [mem_keyFinset_iff, mem_iff_mem_toKeyList, hkeys, List.mem_append,
      List.mem_singleton, Finset.mem_insert]
    tauto
  rw [everKeys_cons, everKeys_eq_biUnion, hkf]
  ext y
  simp [opInsSet]

private def labelRange (a : ℕ) : BinaryTree Unit → BinaryTree ℕ
  | .nil => .nil
  | .node _ l r =>
    let k := a + l.num_nodes
    .node k (labelRange a l) (labelRange (k + 1) r)

private theorem labelRange_shape (a : ℕ) (u : BinaryTree Unit) :
    (labelRange a u).map (fun _ => ()) = u := by
  induction u generalizing a with
  | nil => rfl
  | node u0 l r ihl ihr =>
    cases u0
    simp [labelRange, BinaryTree.map, ihl, ihr]

private theorem labelRange_toKeyList (a : ℕ) (u : BinaryTree Unit) :
    (labelRange a u).toKeyList = List.range' a u.num_nodes := by
  induction u generalizing a with
  | nil => rfl
  | node _ l r ihl ihr =>
    simp only [labelRange, toKeyList, ihl, ihr, num_nodes]
    have h1 : List.range' a l.num_nodes ++ [a + l.num_nodes] =
        List.range' a (l.num_nodes + 1) := by
      have hr := List.range'_append (s := a) (m := l.num_nodes) (n := 1) (step := 1)
      simpa only [Nat.one_mul, List.range'_one] using hr
    have h2 : List.range' a (l.num_nodes + 1) ++ List.range' (a + l.num_nodes + 1) r.num_nodes =
        List.range' a (l.num_nodes + 1 + r.num_nodes) := by
      have hr := List.range'_append (s := a) (m := l.num_nodes + 1)
        (n := r.num_nodes) (step := 1)
      have ha : a + (l.num_nodes + 1) = a + l.num_nodes + 1 := by omega
      simpa only [Nat.one_mul, ha] using hr
    have h3 : l.num_nodes + 1 + r.num_nodes = 1 + l.num_nodes + r.num_nodes := by omega
    rw [h1, h2, h3]

private theorem range'_pairwise_lt (a n : ℕ) : (List.range' a n).Pairwise (· < ·) := by
  induction n generalizing a with
  | zero => simp
  | succ k ih =>
    simp only [List.range'_succ, List.pairwise_cons]
    refine ⟨fun y hy => ?_, ih (a + 1)⟩
    rw [List.mem_range'] at hy
    rcases hy with ⟨i, _, rfl⟩
    omega

private theorem unit_map_eq_nil_iff {α : Type} (t : BinaryTree α) :
    t.map (fun _ => ()) = .nil ↔ t = .nil := by
  cases t <;> simp [BinaryTree.map]

private theorem exists_nested_opsR {α : Type} [LinearOrder α] :
    ∀ (m : ℕ) (t0 : BinaryTree α) (ops : Fin m → DequeOp α)
      (T0 : BinaryTree ℝ) (L0 R0 : ℝ),
      t0.IsBST →
      ValidDequeSeq t0 ops →
      T0.IsBST →
      T0.map (fun _ => ()) = t0.map (fun _ => ()) →
      L0 < R0 →
      (∀ u ∈ T0, L0 < u ∧ u < R0) →
      ∃ (opsR : Fin m → DequeOp ℝ) (Lm Rm : ℝ),
        Lm < Rm ∧
        L0 ≤ Lm ∧ Rm ≤ R0 ∧
        (∀ u ∈ everKeys T0 opsR, L0 < u ∧ u < R0) ∧
        (∀ i : Fin m, DequeOp.sameKind (ops i) (opsR i)) ∧
        ValidDequeSeq T0 opsR ∧
        (∀ t : Fin (m + 1), (dequeSeq T0 opsR t).IsBST) ∧
        (∀ t : Fin (m + 1),
          (dequeSeq T0 opsR t).map (fun _ => ()) = (dequeSeq t0 ops t).map (fun _ => ())) ∧
        dequeSequenceCost T0 opsR = dequeSequenceCost t0 ops ∧
        (∀ t : Fin (m + 1),
          (open Classical in keyFinset (dequeSeq T0 opsR t)) ⊆ everKeys T0 opsR) ∧
        (everKeys T0 opsR).card + (popCount ops + ejectCount ops) = t0.num_nodes + m ∧
        (open Classical in keyFinset (dequeSeq T0 opsR (Fin.last m))) =
          (everKeys T0 opsR).filter (fun u => Lm < u ∧ u < Rm) ∧
        ((popDeletedKeys T0 opsR).Pairwise (· < ·) ∧
          (popDeletedKeys T0 opsR).length = popCount ops ∧
          (open Classical in (popDeletedKeys T0 opsR).toFinset) =
            (everKeys T0 opsR).filter (· ≤ Lm)) ∧
        ((ejectDeletedKeys T0 opsR).Pairwise (· > ·) ∧
          (ejectDeletedKeys T0 opsR).length = ejectCount ops ∧
          (open Classical in (ejectDeletedKeys T0 opsR).toFinset) =
            (everKeys T0 opsR).filter (Rm ≤ ·))
  | 0, t0, ops, T0, L0, R0, _, _, hT0, hShape0, hLR0, hIn0 => by
    classical
    let opsR : Fin 0 → DequeOp ℝ := Fin.elim0
    have hever0 : everKeys T0 opsR = keyFinset T0 := by
      ext u
      simp [everKeys]
    have hnodes0 : T0.num_nodes = t0.num_nodes := by
      have h := congrArg BinaryTree.num_nodes hShape0
      simpa only [map_num_nodes] using h
    refine ⟨opsR, L0, R0, hLR0, le_rfl, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [hever0, mem_keyFinset_iff] at hu
      exact hIn0 u hu
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro t
      rcases Fin.eq_zero t with rfl
      exact hT0
    · intro t
      rcases Fin.eq_zero t with rfl
      exact hShape0
    · simp [dequeSequenceCost]
    · intro t
      rcases Fin.eq_zero t with rfl
      rw [hever0]
      exact Finset.Subset.refl _
    · rw [hever0, card_keyFinset_of_isBST T0 hT0, hnodes0]
      simp [popCount, ejectCount]
    · rw [hever0]
      ext u
      change u ∈ keyFinset T0 ↔ u ∈ (keyFinset T0).filter (fun u => L0 < u ∧ u < R0)
      rw [Finset.mem_filter]
      exact ⟨fun hu => ⟨hu, hIn0 u ((mem_keyFinset_iff T0 u).mp hu)⟩, fun h => h.1⟩
    · refine ⟨by simp [popDeletedKeys], by simp [popDeletedKeys, popCount], ?_⟩
      rw [hever0]
      ext u
      simp only [popDeletedKeys, List.finRange_zero, List.filterMap_nil, List.toFinset_nil,
        Finset.notMem_empty, Finset.mem_filter, mem_keyFinset_iff, false_iff, not_and]
      intro hu hle
      exact not_lt_of_ge hle (hIn0 u hu).1
    · refine ⟨by simp [ejectDeletedKeys], by simp [ejectDeletedKeys, ejectCount], ?_⟩
      rw [hever0]
      ext u
      simp only [ejectDeletedKeys, List.finRange_zero, List.filterMap_nil, List.toFinset_nil,
        Finset.notMem_empty, Finset.mem_filter, mem_keyFinset_iff, false_iff, not_and]
      intro hu hge
      exact not_lt_of_ge hge (hIn0 u hu).2
  | m + 1, t0, ops, T0, L0, R0, ht0, hValid, hT0, hShape0, hLR0, hIn0 => by
    classical
    obtain ⟨hv0, hValid'⟩ := (validDequeSeq_cons_iff t0 ops).mp hValid
    have hnodes0 : T0.num_nodes = t0.num_nodes := by
      have h := congrArg BinaryTree.num_nodes hShape0
      simpa only [map_num_nodes] using h
    cases hop0 : ops 0 with
    | push k_a =>
      rw [hop0] at hv0 hValid'
      have hv0' : ∀ y ∈ t0, k_a < y := hv0
      have ht1 : (SplayTree.push t0 k_a).IsBST := isBST_push t0 k_a ht0 hv0'
      let q : ℝ := match T0.minKey? with
        | none => (L0 + R0) / 2
        | some mn => (L0 + mn) / 2
      have hq_bounds : L0 < q ∧ q < R0 ∧ ∀ y ∈ T0, q < y := by
        cases hmin : T0.minKey? with
        | none =>
          have hnil : T0 = .nil := (minKey?_eq_none_iff T0).mp hmin
          dsimp only [q]; rw [hmin]; dsimp only
          refine ⟨by linarith, by linarith, fun y hy => ?_⟩
          rw [hnil] at hy; simp at hy
        | some mn =>
          have hmn_in : mn ∈ T0 := minKey?_mem T0 mn hmin
          have hmn_b := hIn0 mn hmn_in
          have hmn_le := minKey?_le_of_isBST T0 mn hT0 hmin
          dsimp only [q]; rw [hmin]; dsimp only
          refine ⟨by linarith, by linarith, fun y hy => ?_⟩
          have := hmn_le y hy
          linarith
      let T1 := SplayTree.push T0 q
      have hT1 : T1.IsBST := isBST_push T0 q hT0 hq_bounds.2.2
      have hShape1 : T1.map (fun _ => ()) = (SplayTree.push t0 k_a).map (fun _ => ()) := by
        simp [T1, SplayTree.push, BinaryTree.map, hShape0]
      have hIn1 : ∀ u ∈ T1, L0 < u ∧ u < R0 := by
        intro u hu
        simp only [T1, SplayTree.push, mem_node_iff, not_mem_nil, false_or] at hu
        rcases hu with rfl | hu'
        · exact ⟨hq_bounds.1, hq_bounds.2.1⟩
        · exact hIn0 u hu'
      obtain ⟨opsR', Lm, Rm, hLmRm, hL0Lm, hRmR0, hEverIn', hKind', hValidR',
          hBST', hShape', hCost', hActive', hCard', hSurv', hPop', hEj'⟩ :=
        exists_nested_opsR m (SplayTree.push t0 k_a) (fun j => ops j.succ)
          T1 L0 R0 ht1 hValid' hT1 hShape1 hLR0 hIn1
      let opsR : Fin (m + 1) → DequeOp ℝ := Fin.cons (.push q) opsR'
      have hever_eq : everKeys T0 opsR = everKeys T1 opsR' := everKeys_cons_push T0 q opsR'
      refine ⟨opsR, Lm, Rm, hLmRm, hL0Lm, hRmR0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hever_eq]; exact hEverIn'
      · intro i
        refine Fin.cases ?_ ?_ i
        · simp [opsR, hop0, DequeOp.sameKind]
        · intro j; simpa [opsR] using hKind' j
      · rw [validDequeSeq_cons_iff]
        refine ⟨hq_bounds.2.2, ?_⟩
        simpa [opsR, DequeOp.step, T1] using hValidR'
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact hT0
        · intro j
          rw [dequeSeq_succ_cons]
          simpa [opsR, DequeOp.step, T1] using hBST' j
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact hShape0
        · intro j
          rw [dequeSeq_succ_cons, dequeSeq_succ_cons, hop0]
          simpa [opsR, DequeOp.step, T1] using hShape' j
      · rw [dequeSequenceCost_cons, dequeSequenceCost_cons, hop0]
        simpa [opsR, DequeOp.cost, DequeOp.step, T1] using hCost'
      · intro t
        refine Fin.cases ?_ ?_ t
        · rw [hever_eq]
          intro u hu
          have hu1 : u ∈ keyFinset T1 := by
            rw [mem_keyFinset_iff] at hu ⊢
            exact .right hu
          exact hActive' 0 hu1
        · intro j
          rw [hever_eq, dequeSeq_succ_cons]
          simpa [opsR, DequeOp.step, T1] using hActive' j
      · rw [hever_eq, popCount_cons, ejectCount_cons, hop0]
        simp only [DequeOp.isPop, DequeOp.isEject, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        have hstep_nodes : (SplayTree.push t0 k_a).num_nodes = 1 + t0.num_nodes := by
          simp [SplayTree.push, num_nodes]
        omega
      · have hlast : Fin.last (m + 1) = (Fin.last m).succ := rfl
        rw [hever_eq, hlast, dequeSeq_succ_cons]
        simpa [opsR, DequeOp.step, T1] using hSurv'
      · have hp_eq : popDeletedKeys T0 opsR = popDeletedKeys T1 opsR' := by
          rw [popDeletedKeys_cons]
          simp [opsR, DequeOp.isPop, DequeOp.step, T1]
        have hpc_eq : popCount ops = popCount (fun j => ops j.succ) := by
          rw [popCount_cons, hop0]
          simp [DequeOp.isPop]
        rw [hp_eq, hpc_eq, hever_eq]
        exact hPop'
      · have he_eq : ejectDeletedKeys T0 opsR = ejectDeletedKeys T1 opsR' := by
          rw [ejectDeletedKeys_cons]
          simp [opsR, DequeOp.isEject, DequeOp.step, T1]
        have hec_eq : ejectCount ops = ejectCount (fun j => ops j.succ) := by
          rw [ejectCount_cons, hop0]
          simp [DequeOp.isEject]
        rw [he_eq, hec_eq, hever_eq]
        exact hEj'
    | inject k_a =>
      rw [hop0] at hv0 hValid'
      have hv0' : ∀ y ∈ t0, y < k_a := hv0
      have ht1 : (SplayTree.inject t0 k_a).IsBST := isBST_inject t0 k_a ht0 hv0'
      let q : ℝ := match T0.maxKey? with
        | none => (L0 + R0) / 2
        | some mx => (mx + R0) / 2
      have hq_bounds : L0 < q ∧ q < R0 ∧ ∀ y ∈ T0, y < q := by
        cases hmax : T0.maxKey? with
        | none =>
          have hnil : T0 = .nil := (maxKey?_eq_none_iff T0).mp hmax
          dsimp only [q]; rw [hmax]; dsimp only
          refine ⟨by linarith, by linarith, fun y hy => ?_⟩
          rw [hnil] at hy; simp at hy
        | some mx =>
          have hT0_ne : T0 ≠ .nil := fun h => by simp [h, BinaryTree.maxKey?] at hmax
          obtain ⟨z, hz_max, hz_mem, hz_ge, _, _, _, _, _, _⟩ := eject_spec_poly T0 hT0 hT0_ne
          rw [hmax] at hz_max; rcases Option.some.inj hz_max with rfl
          have hmx_b := hIn0 mx hz_mem
          dsimp only [q]; rw [hmax]; dsimp only
          refine ⟨by linarith, by linarith, fun y hy => ?_⟩
          have := hz_ge y hy
          linarith
      let T1 := SplayTree.inject T0 q
      have hT1 : T1.IsBST := isBST_inject T0 q hT0 hq_bounds.2.2
      have hShape1 : T1.map (fun _ => ()) = (SplayTree.inject t0 k_a).map (fun _ => ()) := by
        simp [T1, SplayTree.inject, BinaryTree.map, hShape0]
      have hIn1 : ∀ u ∈ T1, L0 < u ∧ u < R0 := by
        intro u hu
        simp only [T1, SplayTree.inject, mem_node_iff, not_mem_nil, or_false] at hu
        rcases hu with rfl | hu'
        · exact ⟨hq_bounds.1, hq_bounds.2.1⟩
        · exact hIn0 u hu'
      obtain ⟨opsR', Lm, Rm, hLmRm, hL0Lm, hRmR0, hEverIn', hKind', hValidR',
          hBST', hShape', hCost', hActive', hCard', hSurv', hPop', hEj'⟩ :=
        exists_nested_opsR m (SplayTree.inject t0 k_a) (fun j => ops j.succ)
          T1 L0 R0 ht1 hValid' hT1 hShape1 hLR0 hIn1
      let opsR : Fin (m + 1) → DequeOp ℝ := Fin.cons (.inject q) opsR'
      have hever_eq : everKeys T0 opsR = everKeys T1 opsR' := everKeys_cons_inject T0 q opsR'
      refine ⟨opsR, Lm, Rm, hLmRm, hL0Lm, hRmR0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hever_eq]; exact hEverIn'
      · intro i
        refine Fin.cases ?_ ?_ i
        · simp [opsR, hop0, DequeOp.sameKind]
        · intro j; simpa [opsR] using hKind' j
      · rw [validDequeSeq_cons_iff]
        refine ⟨hq_bounds.2.2, ?_⟩
        simpa [opsR, DequeOp.step, T1] using hValidR'
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact hT0
        · intro j
          rw [dequeSeq_succ_cons]
          simpa [opsR, DequeOp.step, T1] using hBST' j
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact hShape0
        · intro j
          rw [dequeSeq_succ_cons, dequeSeq_succ_cons, hop0]
          simpa [opsR, DequeOp.step, T1] using hShape' j
      · rw [dequeSequenceCost_cons, dequeSequenceCost_cons, hop0]
        simpa [opsR, DequeOp.cost, DequeOp.step, T1] using hCost'
      · intro t
        refine Fin.cases ?_ ?_ t
        · rw [hever_eq]
          intro u hu
          have hu1 : u ∈ keyFinset T1 := by
            rw [mem_keyFinset_iff] at hu ⊢
            exact .left hu
          exact hActive' 0 hu1
        · intro j
          rw [hever_eq, dequeSeq_succ_cons]
          simpa [opsR, DequeOp.step, T1] using hActive' j
      · rw [hever_eq, popCount_cons, ejectCount_cons, hop0]
        simp only [DequeOp.isPop, DequeOp.isEject, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        have hstep_nodes : (SplayTree.inject t0 k_a).num_nodes = 1 + t0.num_nodes := by
          simp [SplayTree.inject, num_nodes]
        omega
      · have hlast : Fin.last (m + 1) = (Fin.last m).succ := rfl
        rw [hever_eq, hlast, dequeSeq_succ_cons]
        simpa [opsR, DequeOp.step, T1] using hSurv'
      · have hp_eq : popDeletedKeys T0 opsR = popDeletedKeys T1 opsR' := by
          rw [popDeletedKeys_cons]
          simp [opsR, DequeOp.isPop, DequeOp.step, T1]
        have hpc_eq : popCount ops = popCount (fun j => ops j.succ) := by
          rw [popCount_cons, hop0]
          simp [DequeOp.isPop]
        rw [hp_eq, hpc_eq, hever_eq]
        exact hPop'
      · have he_eq : ejectDeletedKeys T0 opsR = ejectDeletedKeys T1 opsR' := by
          rw [ejectDeletedKeys_cons]
          simp [opsR, DequeOp.isEject, DequeOp.step, T1]
        have hec_eq : ejectCount ops = ejectCount (fun j => ops j.succ) := by
          rw [ejectCount_cons, hop0]
          simp [DequeOp.isEject]
        rw [he_eq, hec_eq, hever_eq]
        exact hEj'
    | pop =>
      rw [hop0] at hv0 hValid'
      have ht0_ne : t0 ≠ .nil := hv0
      have hT0_ne : T0 ≠ .nil := by
        intro h; apply ht0_ne
        rw [← unit_map_eq_nil_iff, ← hShape0, h]; rfl
      obtain ⟨_, _, _, _, ht_pop_eq, ht_cost_eq, _, ht1, _, ht1_nodes⟩ :=
        pop_spec_poly t0 ht0 ht0_ne
      obtain ⟨x, hx_min, hx_mem, _, hT_pop_eq, hT_cost_eq, hT_keys, hT1, hT1_gt, _⟩ :=
        pop_spec_poly T0 hT0 hT0_ne
      have hx_b := hIn0 x hx_mem
      let T1 := SplayTree.pop T0
      have hShape1 : T1.map (fun _ => ()) = (SplayTree.pop t0).map (fun _ => ()) := by
        dsimp only [T1]
        rw [hT_pop_eq, ht_pop_eq, popPoly_map, popPoly_map, hShape0]
      have hIn1 : ∀ u ∈ T1, x < u ∧ u < R0 := by
        intro u hu
        have hu_in0 : u ∈ T0 := by
          rw [mem_iff_mem_toKeyList, hT_keys, List.mem_cons]
          exact Or.inr (mem_iff_mem_toKeyList.mp hu)
        exact ⟨hT1_gt u hu, (hIn0 u hu_in0).2⟩
      obtain ⟨opsR', Lm, Rm, hLmRm, hxLm, hRmR0, hEverIn', hKind', hValidR',
          hBST', hShape', hCost', hActive', hCard', hSurv', hPop', hEj'⟩ :=
        exists_nested_opsR m (SplayTree.pop t0) (fun j => ops j.succ)
          T1 x R0 ht1 hValid' hT1 hShape1 hx_b.2 hIn1
      let opsR : Fin (m + 1) → DequeOp ℝ := Fin.cons .pop opsR'
      have hever_eq : everKeys T0 opsR = insert x (everKeys T1 opsR') :=
        everKeys_cons_pop T0 x opsR' hT_keys
      have hx_not_mem : x ∉ everKeys T1 opsR' := by
        intro hx_in
        exact lt_irrefl x (hEverIn' x hx_in).1
      refine ⟨opsR, Lm, Rm, hLmRm, le_trans (le_of_lt hx_b.1) hxLm, hRmR0,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rw [hever_eq, Finset.mem_insert] at hu
        rcases hu with rfl | hu'
        · exact hx_b
        · exact ⟨lt_trans hx_b.1 (hEverIn' u hu').1, (hEverIn' u hu').2⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · simp [opsR, hop0, DequeOp.sameKind]
        · intro j; simpa [opsR] using hKind' j
      · rw [validDequeSeq_cons_iff]
        refine ⟨hT0_ne, ?_⟩
        simpa [opsR, DequeOp.step, T1] using hValidR'
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact hT0
        · intro j
          rw [dequeSeq_succ_cons]
          simpa [opsR, DequeOp.step, T1] using hBST' j
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact hShape0
        · intro j
          rw [dequeSeq_succ_cons, dequeSeq_succ_cons, hop0]
          simpa [opsR, DequeOp.step, T1] using hShape' j
      · rw [dequeSequenceCost_cons, dequeSequenceCost_cons, hop0]
        have hc0 : popCost T0 = popCost t0 := by
          rw [hT_cost_eq, ht_cost_eq, hShape0]
        have htail_eq : dequeSequenceCost ((opsR 0).step T0) (fun j => opsR j.succ) =
            dequeSequenceCost (SplayTree.pop t0) (fun j => ops j.succ) := by
          simpa [opsR, DequeOp.step, T1] using hCost'
        simp only [opsR, Fin.cons_zero, DequeOp.cost] at htail_eq ⊢
        rw [hc0, htail_eq]
        rfl
      · intro t
        refine Fin.cases ?_ ?_ t
        · rw [hever_eq]
          intro u hu
          change u ∈ keyFinset T0 at hu
          rw [mem_keyFinset_iff, mem_iff_mem_toKeyList, hT_keys, List.mem_cons] at hu
          rcases hu with rfl | hu'
          · exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (hActive' 0 ?_)
            change u ∈ keyFinset T1
            rw [mem_keyFinset_iff, mem_iff_mem_toKeyList]
            exact hu'
        · intro j
          rw [hever_eq, dequeSeq_succ_cons]
          intro u hu
          refine Finset.mem_insert_of_mem ?_
          simpa [opsR, DequeOp.step, T1] using hActive' j hu
      · rw [hever_eq, Finset.card_insert_of_notMem hx_not_mem, popCount_cons, ejectCount_cons, hop0]
        simp only [DequeOp.isPop, DequeOp.isEject, ↓reduceIte, Bool.false_eq_true, Nat.zero_add]
        omega
      · have hlast : Fin.last (m + 1) = (Fin.last m).succ := rfl
        rw [hever_eq, Finset.filter_insert]
        have hnot_mid : ¬(Lm < x ∧ x < Rm) := fun h => not_lt_of_ge hxLm h.1
        simp only [hnot_mid, ↓reduceIte]
        rw [hlast, dequeSeq_succ_cons]
        simpa [opsR, DequeOp.step, T1] using hSurv'
      · have hp_eq : popDeletedKeys T0 opsR = x :: popDeletedKeys T1 opsR' := by
          rw [popDeletedKeys_cons]
          simp [opsR, DequeOp.isPop, hx_min, DequeOp.step, T1]
        have hpc_eq : popCount ops = 1 + popCount (fun j => ops j.succ) := by
          rw [popCount_cons, hop0]
          simp [DequeOp.isPop]
        rw [hp_eq, hpc_eq, hever_eq, Finset.filter_insert]
        simp only [hxLm, ↓reduceIte]
        refine ⟨List.pairwise_cons.mpr ⟨?_, hPop'.1⟩, ?_, ?_⟩
        · intro y hy
          have hy_in : y ∈ (popDeletedKeys T1 opsR').toFinset := List.mem_toFinset.mpr hy
          rw [hPop'.2.2, Finset.mem_filter] at hy_in
          exact (hEverIn' y hy_in.1).1
        · rw [List.length_cons, hPop'.2.1]; omega
        · rw [List.toFinset_cons, hPop'.2.2]
      · have he_eq : ejectDeletedKeys T0 opsR = ejectDeletedKeys T1 opsR' := by
          rw [ejectDeletedKeys_cons]
          simp [opsR, DequeOp.isEject, DequeOp.step, T1]
        have hec_eq : ejectCount ops = ejectCount (fun j => ops j.succ) := by
          rw [ejectCount_cons, hop0]
          simp [DequeOp.isEject]
        rw [he_eq, hec_eq, hever_eq, Finset.filter_insert]
        have hnot_ge : ¬(Rm ≤ x) := not_le_of_gt (lt_of_le_of_lt hxLm hLmRm)
        simp only [hnot_ge, ↓reduceIte]
        exact hEj'
    | eject =>
      rw [hop0] at hv0 hValid'
      have ht0_ne : t0 ≠ .nil := hv0
      have hT0_ne : T0 ≠ .nil := by
        intro h; apply ht0_ne
        rw [← unit_map_eq_nil_iff, ← hShape0, h]; rfl
      obtain ⟨_, _, _, _, ht_ej_eq, ht_cost_eq, _, ht1, _, ht1_nodes⟩ :=
        eject_spec_poly t0 ht0 ht0_ne
      obtain ⟨z, hz_max, hz_mem, _, hT_ej_eq, hT_cost_eq, hT_keys, hT1, hT1_lt, _⟩ :=
        eject_spec_poly T0 hT0 hT0_ne
      have hz_b := hIn0 z hz_mem
      let T1 := SplayTree.eject T0
      have hShape1 : T1.map (fun _ => ()) = (SplayTree.eject t0).map (fun _ => ()) := by
        dsimp only [T1]
        rw [hT_ej_eq, ht_ej_eq, ejectPoly_map, ejectPoly_map, hShape0]
      have hIn1 : ∀ u ∈ T1, L0 < u ∧ u < z := by
        intro u hu
        have hu_in0 : u ∈ T0 := by
          rw [mem_iff_mem_toKeyList, hT_keys, List.mem_append]
          exact Or.inl (mem_iff_mem_toKeyList.mp hu)
        exact ⟨(hIn0 u hu_in0).1, hT1_lt u hu⟩
      obtain ⟨opsR', Lm, Rm, hLmRm, hL0Lm, hRmz, hEverIn', hKind', hValidR',
          hBST', hShape', hCost', hActive', hCard', hSurv', hPop', hEj'⟩ :=
        exists_nested_opsR m (SplayTree.eject t0) (fun j => ops j.succ)
          T1 L0 z ht1 hValid' hT1 hShape1 hz_b.1 hIn1
      let opsR : Fin (m + 1) → DequeOp ℝ := Fin.cons .eject opsR'
      have hever_eq : everKeys T0 opsR = insert z (everKeys T1 opsR') :=
        everKeys_cons_eject T0 z opsR' hT_keys
      have hz_not_mem : z ∉ everKeys T1 opsR' := by
        intro hz_in
        exact lt_irrefl z (hEverIn' z hz_in).2
      refine ⟨opsR, Lm, Rm, hLmRm, hL0Lm, le_trans hRmz (le_of_lt hz_b.2),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rw [hever_eq, Finset.mem_insert] at hu
        rcases hu with rfl | hu'
        · exact hz_b
        · exact ⟨(hEverIn' u hu').1, lt_trans (hEverIn' u hu').2 hz_b.2⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · simp [opsR, hop0, DequeOp.sameKind]
        · intro j; simpa [opsR] using hKind' j
      · rw [validDequeSeq_cons_iff]
        refine ⟨hT0_ne, ?_⟩
        simpa [opsR, DequeOp.step, T1] using hValidR'
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact hT0
        · intro j
          rw [dequeSeq_succ_cons]
          simpa [opsR, DequeOp.step, T1] using hBST' j
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact hShape0
        · intro j
          rw [dequeSeq_succ_cons, dequeSeq_succ_cons, hop0]
          simpa [opsR, DequeOp.step, T1] using hShape' j
      · rw [dequeSequenceCost_cons, dequeSequenceCost_cons, hop0]
        have hc0 : ejectCost T0 = ejectCost t0 := by
          rw [hT_cost_eq, ht_cost_eq, hShape0]
        have htail_eq : dequeSequenceCost ((opsR 0).step T0) (fun j => opsR j.succ) =
            dequeSequenceCost (SplayTree.eject t0) (fun j => ops j.succ) := by
          simpa [opsR, DequeOp.step, T1] using hCost'
        simp only [opsR, Fin.cons_zero, DequeOp.cost] at htail_eq ⊢
        rw [hc0, htail_eq]
        rfl
      · intro t
        refine Fin.cases ?_ ?_ t
        · rw [hever_eq]
          intro u hu
          change u ∈ keyFinset T0 at hu
          rw [mem_keyFinset_iff, mem_iff_mem_toKeyList, hT_keys, List.mem_append,
            List.mem_singleton] at hu
          rcases hu with hu' | rfl
          · refine Finset.mem_insert_of_mem (hActive' 0 ?_)
            change u ∈ keyFinset T1
            rw [mem_keyFinset_iff, mem_iff_mem_toKeyList]
            exact hu'
          · exact Finset.mem_insert_self _ _
        · intro j
          rw [hever_eq, dequeSeq_succ_cons]
          intro u hu
          refine Finset.mem_insert_of_mem ?_
          simpa [opsR, DequeOp.step, T1] using hActive' j hu
      · rw [hever_eq, Finset.card_insert_of_notMem hz_not_mem, popCount_cons, ejectCount_cons, hop0]
        simp only [DequeOp.isPop, DequeOp.isEject, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        omega
      · have hlast : Fin.last (m + 1) = (Fin.last m).succ := rfl
        rw [hever_eq, Finset.filter_insert]
        have hnot_mid : ¬(Lm < z ∧ z < Rm) := fun h => not_lt_of_ge hRmz h.2
        simp only [hnot_mid, ↓reduceIte]
        rw [hlast, dequeSeq_succ_cons]
        simpa [opsR, DequeOp.step, T1] using hSurv'
      · have hp_eq : popDeletedKeys T0 opsR = popDeletedKeys T1 opsR' := by
          rw [popDeletedKeys_cons]
          simp [opsR, DequeOp.isPop, DequeOp.step, T1]
        have hpc_eq : popCount ops = popCount (fun j => ops j.succ) := by
          rw [popCount_cons, hop0]
          simp [DequeOp.isPop]
        rw [hp_eq, hpc_eq, hever_eq, Finset.filter_insert]
        have hnot_le : ¬(z ≤ Lm) := not_le_of_gt (lt_of_lt_of_le hLmRm hRmz)
        simp only [hnot_le, ↓reduceIte]
        exact hPop'
      · have he_eq : ejectDeletedKeys T0 opsR = z :: ejectDeletedKeys T1 opsR' := by
          rw [ejectDeletedKeys_cons]
          simp [opsR, DequeOp.isEject, hz_max, DequeOp.step, T1]
        have hec_eq : ejectCount ops = 1 + ejectCount (fun j => ops j.succ) := by
          rw [ejectCount_cons, hop0]
          simp [DequeOp.isEject]
        rw [he_eq, hec_eq, hever_eq, Finset.filter_insert]
        simp only [hRmz, ↓reduceIte]
        refine ⟨List.pairwise_cons.mpr ⟨?_, hEj'.1⟩, ?_, ?_⟩
        · intro y hy
          have hy_in : y ∈ (ejectDeletedKeys T1 opsR').toFinset := List.mem_toFinset.mpr hy
          rw [hEj'.2.2, Finset.mem_filter] at hy_in
          exact (hEverIn' y hy_in.1).2
        · rw [List.length_cons, hEj'.2.1]; omega
        · rw [List.toFinset_cons, hEj'.2.2]

/-- **Lemma 3.3** (`lem:nested-keys`, Offline Nested-Interval Three-Way Key Assignment):
Every valid `m`-operation deque sequence `(init, ops)` on an `n`-node BST admits an offline
three-way real key assignment `V_L ⊔ V_M ⊔ V_R` (`Lm < Rm`) preserving all BST shapes and
rotation costs, with `|V_L| = d_L` in chronological `POP` order, `|V_M| = n + m - 2d` surviving
in `T_m`, `|V_R| = d_R` in reverse chronological `EJECT` order, and `V_L < V_M < V_R`. -/
theorem lem_3_3_nested_keys {α : Type} [LinearOrder α] {m : ℕ}
    (init : BST α) (ops : Fin m → DequeOp α) (hValid : ValidDequeSeq init.tree ops) :
    ∃ asn : ThreeWayKeyAssignment init ops,
      asn.VL.card = popCount ops ∧
      asn.VM.card + 2 * (popCount ops + ejectCount ops) = init.tree.num_nodes + m ∧
      asn.VR.card = ejectCount ops ∧
      asn.everPresentKeys = asn.VL ∪ asn.VM ∪ asn.VR ∧
      (∀ x ∈ asn.VL, ∀ y ∈ asn.VM, x < y) ∧
      (∀ y ∈ asn.VM, ∀ z ∈ asn.VR, y < z) := by
  classical
  let u0 := init.tree.map (fun _ => ())
  let T0 : BinaryTree ℝ := (labelRange 1 u0).map (fun k : ℕ => (k : ℝ))
  let L0 : ℝ := 0
  let R0 : ℝ := (init.tree.num_nodes : ℝ) + 1
  have hT0_bst : T0.IsBST := by
    rw [IsBST_iff_toKeyList_sorted, toKeyList_map, labelRange_toKeyList, List.pairwise_map]
    exact (range'_pairwise_lt 1 u0.num_nodes).imp (fun {a b} hab => Nat.cast_lt.mpr hab)
  have hT0_shape : T0.map (fun _ => ()) = init.tree.map (fun _ => ()) := by
    dsimp only [T0]
    rw [map_map]
    exact labelRange_shape 1 u0
  have hLR0 : L0 < R0 := by
    dsimp only [L0, R0]
    positivity
  have hIn0 : ∀ u ∈ T0, L0 < u ∧ u < R0 := by
    intro u hu
    dsimp only [T0] at hu
    rw [mem_map_iff] at hu
    rcases hu with ⟨k, hk, rfl⟩
    rw [mem_iff_mem_toKeyList, labelRange_toKeyList, map_num_nodes, List.mem_range'] at hk
    rcases hk with ⟨i, hi, rfl⟩
    simp only [Nat.one_mul]
    dsimp only [L0, R0]
    constructor
    · exact_mod_cast (by omega : 0 < 1 + i)
    · exact_mod_cast (by omega : 1 + i < init.tree.num_nodes + 1)
  obtain ⟨opsR, Lm, Rm, hLmRm, _, _, _, hKind, hValidR,
      hBST, hShape, hCost, hActive, hCard, hSurv, hPop, hEj⟩ :=
    exists_nested_opsR m init.tree ops T0 L0 R0 init.hBST hValid hT0_bst hT0_shape hLR0 hIn0
  let asn : ThreeWayKeyAssignment init ops :=
    { T0 := T0
      opsR := opsR
      Lm := Lm
      Rm := Rm
      hLmRm := hLmRm
      hKind := hKind
      hValidR := hValidR
      hBST := hBST
      hShape := hShape
      hCost := hCost
      hActiveSub := hActive
      hEverCard := hCard
      hSurviving := hSurv
      hPopOrder := hPop
      hEjectOrder := hEj }
  have hVL_card : asn.VL.card = popCount ops := by
    have hnodup : (popDeletedKeys T0 opsR).Nodup := hPop.1.imp ne_of_lt
    have hc : (popDeletedKeys T0 opsR).toFinset.card = (popDeletedKeys T0 opsR).length :=
      List.toFinset_card_of_nodup hnodup
    change ((everKeys T0 opsR).filter (· ≤ Lm)).card = popCount ops
    rw [← hPop.2.2, hc, hPop.2.1]
  have hVR_card : asn.VR.card = ejectCount ops := by
    have hnodup : (ejectDeletedKeys T0 opsR).Nodup := hEj.1.imp (fun h => ne_of_gt h)
    have hc : (ejectDeletedKeys T0 opsR).toFinset.card = (ejectDeletedKeys T0 opsR).length :=
      List.toFinset_card_of_nodup hnodup
    change ((everKeys T0 opsR).filter (Rm ≤ ·)).card = ejectCount ops
    rw [← hEj.2.2, hc, hEj.2.1]
  have hVL_lt_VM : ∀ x ∈ asn.VL, ∀ y ∈ asn.VM, x < y := by
    intro x hx y hy
    simp only [ThreeWayKeyAssignment.VL, ThreeWayKeyAssignment.VM, Finset.mem_filter] at hx hy
    exact lt_of_le_of_lt hx.2 hy.2.1
  have hVM_lt_VR : ∀ y ∈ asn.VM, ∀ z ∈ asn.VR, y < z := by
    intro y hy z hz
    simp only [ThreeWayKeyAssignment.VM, ThreeWayKeyAssignment.VR, Finset.mem_filter] at hy hz
    exact lt_of_lt_of_le hy.2.2 hz.2
  have hunion : asn.everPresentKeys = asn.VL ∪ asn.VM ∪ asn.VR := by
    ext x
    simp only [ThreeWayKeyAssignment.VL, ThreeWayKeyAssignment.VM, ThreeWayKeyAssignment.VR,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      by_cases h1 : x ≤ asn.Lm
      · exact Or.inl (Or.inl ⟨hx, h1⟩)
      · by_cases h2 : asn.Rm ≤ x
        · exact Or.inr ⟨hx, h2⟩
        · exact Or.inl (Or.inr ⟨hx, lt_of_not_ge h1, lt_of_not_ge h2⟩)
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
  have hdisj1 : Disjoint asn.VL asn.VM := by
    rw [Finset.disjoint_left]
    intro x hxL hxM
    exact lt_irrefl x (hVL_lt_VM x hxL x hxM)
  have hdisj2 : Disjoint (asn.VL ∪ asn.VM) asn.VR := by
    rw [Finset.disjoint_left]
    intro x hxLM hxR
    rw [Finset.mem_union] at hxLM
    rcases hxLM with hxL | hxM
    · simp only [ThreeWayKeyAssignment.VL, ThreeWayKeyAssignment.VR,
        Finset.mem_filter] at hxL hxR
      exact not_lt_of_ge (le_trans hxR.2 hxL.2) asn.hLmRm
    · exact lt_irrefl x (hVM_lt_VR x hxM x hxR)
  have hsum_cards : asn.everPresentKeys.card = asn.VL.card + asn.VM.card + asn.VR.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]
  have hVM_card : asn.VM.card + 2 * (popCount ops + ejectCount ops) = init.tree.num_nodes + m := by
    have hc : asn.everPresentKeys.card + (popCount ops + ejectCount ops) =
        init.tree.num_nodes + m := asn.hEverCard
    omega
  exact ⟨asn, hVL_card, hVM_card, hVR_card, hunion, hVL_lt_VM, hVM_lt_VR⟩

/-! ## Section 3: Uncoupled Spine Potential Accounting (Lemma 3.4) -/

/-- Exact statement type of Lemma 3.1 (`Challenge.lem_3_1_bst_projection`). -/
abbrev Ty_lem_3_1 : Prop :=
  ∀ {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α),
    t.IsBST → IsLCAClosed t S →
    ((restrictTree t S).IsBST ∧ ∀ v : α, v ∈ restrictTree t S ↔ v ∈ t ∧ v ∈ S) ∧
    (∀ x y : α, IsSingleRotEdge t x y →
      let t' := rotateEdge t x y
      IsLCAClosed t' S →
        (x ∈ S ∧ y ∈ S →
          IsSingleRotEdge (restrictTree t S) x y ∧
            restrictTree t' S = rotateEdge (restrictTree t S) x y) ∧
        (¬ (x ∈ S ∧ y ∈ S) → restrictTree t' S = restrictTree t S)) ∧
    (t ≠ .nil →
      (let tMin := spliceMin t
       IsLCAClosed tMin S ∧
         ∀ xMin : α, t.minKey? = some xMin →
           (xMin ∈ S →
             (restrictTree t S).minKey? = some xMin ∧
               restrictTree tMin S = spliceMin (restrictTree t S)) ∧
           (xMin ∉ S → restrictTree tMin S = restrictTree t S)) ∧
      (let tMax := spliceMax t
       IsLCAClosed tMax S ∧
         ∀ xMax : α, t.maxKey? = some xMax →
           (xMax ∈ S →
             (restrictTree t S).maxKey? = some xMax ∧
               restrictTree tMax S = spliceMax (restrictTree t S)) ∧
           (xMax ∉ S → restrictTree tMax S = restrictTree t S)))

/-- Exact statement type of Lemma 3.2 (`Challenge.lem_3_2_cascade_equiv`). -/
abbrev Ty_lem_3_2 : Prop :=
  ∀ {α : Type} [LinearOrder α] (t : BinaryTree α),
    t.IsBST → t ≠ .nil →
    (let k := (leftSpine t).length - 1
     let r := k / 2
     (leftSpine t).length = k + 1 ∧
       (k = 2 * r ∨ k = 2 * r + 1) ∧
       (popCascadePairs t).length = r ∧
       popCost t = (k : ℝ) ∧
       SplayTree.pop t = popCascade t) ∧
    (let k' := (rightSpineBottomUp t).length - 1
     let r' := k' / 2
     (rightSpineBottomUp t).length = k' + 1 ∧
       (k' = 2 * r' ∨ k' = 2 * r' + 1) ∧
       (ejectCascadePairs t).length = r' ∧
       ejectCost t = (k' : ℝ) ∧
       SplayTree.eject t = ejectCascade t)

private def OrdConvex {α : Type} [LinearOrder α] (S : Set α) : Prop :=
  ∀ ⦃a b c : α⦄, a ≤ b → b ≤ c → a ∈ S → c ∈ S → b ∈ S

private theorem ordConvex_Iic (L : ℝ) : OrdConvex {x : ℝ | x ≤ L} :=
  fun _ _ _ _ hbc _ hc => le_trans hbc hc

private theorem ordConvex_Ioo (L R : ℝ) : OrdConvex {x : ℝ | L < x ∧ x < R} :=
  fun _ _ _ hab hbc ha hc => ⟨lt_of_lt_of_le ha.1 hab, lt_of_le_of_lt hbc hc.2⟩

private theorem ordConvex_Ici (R : ℝ) : OrdConvex {x : ℝ | R ≤ x} :=
  fun _ _ _ hab _ ha _ => le_trans ha hab

private theorem lcaBST_between {α : Type} [LinearOrder α] (t : BinaryTree α) (x y z : α)
    (h : lcaBST t x y = some z) : (x ≤ z ∧ z ≤ y) ∨ (y ≤ z ∧ z ≤ x) := by
  induction t with
  | nil => simp [lcaBST] at h
  | node k l r ihl ihr =>
    simp only [lcaBST] at h
    by_cases h1 : x < k ∧ y < k
    · simp only [h1, and_self, ↓reduceIte] at h
      exact ihl h
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : k < x ∧ k < y
      · simp only [h2, and_self, ↓reduceIte] at h
        exact ihr h
      · simp only [h2, ↓reduceIte, Option.some.injEq] at h
        subst h
        rcases le_or_gt x k with hxk | hkx
        · rcases le_or_gt k y with hky | hyk
          · exact Or.inl ⟨hxk, hky⟩
          · rcases eq_or_lt_of_le hxk with rfl | hxlt
            · exact Or.inr ⟨le_of_lt hyk, le_rfl⟩
            · exact absurd ⟨hxlt, hyk⟩ h1
        · rcases le_or_gt y k with hyk | hky
          · exact Or.inr ⟨hyk, le_of_lt hkx⟩
          · exact absurd ⟨hkx, hky⟩ h2

private theorem isLCAClosed_of_ordConvex {α : Type} [LinearOrder α] {S : Set α}
    (hS : OrdConvex S) (t : BinaryTree α) : IsLCAClosed t S := by
  intro x _ y _ hxS hyS z hz
  rcases lcaBST_between t x y z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hS h1 h2 hxS hyS
  · exact hS h1 h2 hyS hxS

private theorem restrictTree_eq_nil_of_disjoint {α : Type} (t : BinaryTree α) (S : Set α)
    (h : ∀ x ∈ t, x ∉ S) : restrictTree t S = .nil := by
  classical
  induction t with
  | nil => rfl
  | node u A B ihA ihB =>
    have hu : u ∉ S := h u .here
    have hA : ∀ x ∈ A, x ∉ S := fun x hx => h x (.left hx)
    have hB : ∀ x ∈ B, x ∉ S := fun x hx => h x (.right hx)
    have hnoB : ¬∃ b ∈ B, b ∈ S := fun ⟨b, hb, hbS⟩ => hB b hb hbS
    simp only [restrictTree, hu, hnoB, ↓reduceIte]
    exact ihA hA

private theorem restrictTree_push {α : Type} (t : BinaryTree α) (q : α) (S : Set α) :
    restrictTree (SplayTree.push t q) S =
      (open Classical in if q ∈ S then .node q .nil (restrictTree t S) else restrictTree t S) := by
  classical
  simp only [SplayTree.push, restrictTree]
  by_cases hq : q ∈ S
  · simp [hq]
  · simp only [hq, ↓reduceIte]
    by_cases hB : ∃ b ∈ t, b ∈ S
    · simp [hB]
    · simp only [hB, ↓reduceIte]
      symm
      exact restrictTree_eq_nil_of_disjoint t S (fun b hb hbS => hB ⟨b, hb, hbS⟩)

private theorem restrictTree_inject {α : Type} (t : BinaryTree α) (q : α) (S : Set α) :
    restrictTree (SplayTree.inject t q) S =
      (open Classical in if q ∈ S then .node q (restrictTree t S) .nil else restrictTree t S) := by
  classical
  simp only [SplayTree.inject, restrictTree]
  by_cases hq : q ∈ S
  · simp [hq]
  · simp [hq]

/-! ### Spine Helper Lemmas -/

private theorem mem_leftSpine_mem {α : Type} {t : BinaryTree α} {x : α}
    (h : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at h
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at h
    rcases h with hl | rfl
    · exact .left (ihl hl)
    · exact .here

private theorem mem_rightSpine_mem {α : Type} {t : BinaryTree α} {x : α}
    (h : x ∈ rightSpine t) : x ∈ t := by
  induction t with
  | nil => simp [rightSpine] at h
  | node k l r _ ihr =>
    simp only [rightSpine, List.mem_cons] at h
    rcases h with rfl | hr
    · exact .here
    · exact .right (ihr hr)

private theorem leftSpine_eq_nil_iff {α : Type} (t : BinaryTree α) :
    leftSpine t = [] ↔ t = .nil := by
  cases t <;> simp [leftSpine]

private theorem rightSpine_eq_nil_iff {α : Type} (t : BinaryTree α) :
    rightSpine t = [] ↔ t = .nil := by
  cases t <;> simp [rightSpine]

private theorem leftSpine_length_le_num_nodes {α : Type} (t : BinaryTree α) :
    (leftSpine t).length ≤ t.num_nodes := by
  induction t with
  | nil => simp [leftSpine]
  | node _ l r ihl _ =>
    simp only [leftSpine, List.length_append, List.length_singleton, num_nodes]
    omega

private theorem rightSpine_length_le_num_nodes {α : Type} (t : BinaryTree α) :
    (rightSpine t).length ≤ t.num_nodes := by
  induction t with
  | nil => simp [rightSpine]
  | node _ l r _ ihr =>
    simp only [rightSpine, List.length_cons, num_nodes]
    omega

private theorem leftSpine_sorted {α : Type} [LinearOrder α] (t : BinaryTree α) (ht : t.IsBST) :
    (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    simp only [leftSpine, List.pairwise_append, List.pairwise_singleton]
    refine ⟨ihl (IsBST_left_of_IsBST ht), trivial, fun x hx y hy => ?_⟩
    rw [List.mem_singleton] at hy; subst y
    exact lt_of_IsBST_left l k r ht (mem_leftSpine_mem hx)

private theorem tail_append_of_ne_nil {α : Type} {xs ys : List α} (h : xs ≠ []) :
    (xs ++ ys).tail = xs.tail ++ ys := by
  cases xs with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

private theorem snoc_inj {α : Type} {xs ys : List α} {a b : α}
    (h : xs ++ [a] = ys ++ [b]) : xs = ys ∧ a = b := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  exact ⟨h1, List.singleton_inj.mp h2⟩

private theorem toKeyList_spliceMin {α : Type} (t : BinaryTree α) :
    (spliceMin t).toKeyList = t.toKeyList.tail := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp [spliceMin, toKeyList]
    · have hl_ne : (ll △[lk] lr).toKeyList ≠ [] := by simp [toKeyList]
      have hsp : spliceMin ((ll △[lk] lr) △[k] r) = (spliceMin (ll △[lk] lr)) △[k] r := rfl
      rw [hsp, toKeyList_node, toKeyList_node, ihl]
      rw [List.append_assoc, List.append_assoc, tail_append_of_ne_nil hl_ne]

private theorem isBST_spliceMin {α : Type} [LinearOrder α] (t : BinaryTree α) (ht : t.IsBST) :
    (spliceMin t).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at ht ⊢
  rw [toKeyList_spliceMin]
  cases htkl : t.toKeyList with
  | nil => simp
  | cons a as =>
    rw [htkl] at ht
    exact (List.pairwise_cons.mp ht).2

private theorem leftSpine_spliceMin_suffix {α : Type} (t : BinaryTree α) :
    ∃ pre : List α, leftSpine (spliceMin t) = pre ++ (leftSpine t).tail := by
  induction t with
  | nil => exact ⟨[], rfl⟩
  | node k l r ihl _ =>
    rcases l with _ | ⟨lk, ll, lr⟩
    · exact ⟨leftSpine r, by simp [spliceMin, leftSpine]⟩
    · rcases ihl with ⟨pre, hpre⟩
      have hl_ne : leftSpine ll ++ [lk] ≠ [] := by simp
      refine ⟨pre, ?_⟩
      have hsp : spliceMin ((ll △[lk] lr) △[k] r) = (spliceMin (ll △[lk] lr)) △[k] r := rfl
      rw [hsp]
      simp only [leftSpine, hpre]
      rw [tail_append_of_ne_nil hl_ne, List.append_assoc]

private theorem rightSpine_spliceMin_of_two {α : Type} (t : BinaryTree α)
    (h : 2 ≤ (leftSpine t).length) :
    rightSpine (spliceMin t) = rightSpine t := by
  rcases t with _ | ⟨k, _ | ⟨lk, ll, lr⟩, r⟩
  · simp [leftSpine] at h
  · simp [leftSpine] at h
  · rfl

private theorem leftSpine_restrictTree_suffix {α : Type} [LinearOrder α]
    (t : BinaryTree α) (S : Set α) (ht : t.IsBST) (hS : OrdConvex S) :
    ∃ pre : List α,
      leftSpine (restrictTree t S) =
        pre ++ (open Classical in (leftSpine t).filter (fun x => decide (x ∈ S))) := by
  classical
  induction t with
  | nil => exact ⟨[], by simp [restrictTree, leftSpine]⟩
  | node u A B ihA _ =>
    have hA_bst := IsBST_left_of_IsBST ht
    rcases ihA hA_bst with ⟨preA, hpreA⟩
    by_cases hu : u ∈ S
    · refine ⟨preA, ?_⟩
      simp [restrictTree, hu, leftSpine, hpreA, List.filter_append]
    · by_cases hB : ∃ b ∈ B, b ∈ S
      · refine ⟨leftSpine (restrictTree B S), ?_⟩
        have hA_disj : ∀ a ∈ A, a ∉ S := by
          intro a ha haS
          rcases hB with ⟨b, hb, hbS⟩
          have hau : a ≤ u := le_of_lt (lt_of_IsBST_left A u B ht ha)
          have hub : u ≤ b := le_of_lt (gt_of_IsBST_right A u B ht hb)
          exact hu (hS hau hub haS hbS)
        have hfiltA : (leftSpine A).filter (fun x => decide (x ∈ S)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          simp [hA_disj x (mem_leftSpine_mem hx)]
        simp [restrictTree, hu, hB, leftSpine, List.filter_append, hfiltA]
      · refine ⟨preA, ?_⟩
        simp [restrictTree, hu, hB, leftSpine, List.filter_append, hpreA]

private theorem restrictTree_eq_self_of_all {α : Type} (t : BinaryTree α) (S : Set α)
    (h : ∀ x ∈ t, x ∈ S) : restrictTree t S = t := by
  classical
  induction t with
  | nil => rfl
  | node u A B ihA ihB =>
    have hu : u ∈ S := h u .here
    have hA := ihA (fun x hx => h x (.left hx))
    have hB := ihB (fun x hx => h x (.right hx))
    simp [restrictTree, hu, hA, hB]

private theorem leftSpine_restrictTree_Iic (t : BinaryTree ℝ) (L : ℝ) (ht : t.IsBST) :
    leftSpine (restrictTree t {x : ℝ | x ≤ L}) =
      (open Classical in (leftSpine t).filter (fun x => decide (x ≤ L))) := by
  classical
  induction t with
  | nil => simp [restrictTree, leftSpine]
  | node u A B ihA _ =>
    have hA_bst := IsBST_left_of_IsBST ht
    by_cases hu : u ≤ L
    · have huS : u ∈ ({x : ℝ | x ≤ L} : Set ℝ) := hu
      have hA_all : ∀ a ∈ A, a ≤ L :=
        fun a ha => le_trans (le_of_lt (lt_of_IsBST_left A u B ht ha)) hu
      have hA_eq : restrictTree A {x : ℝ | x ≤ L} = A :=
        restrictTree_eq_self_of_all A {x : ℝ | x ≤ L} hA_all
      have hfiltA : (leftSpine A).filter (fun x => decide (x ≤ L)) = leftSpine A := by
        rw [List.filter_eq_self]
        intro x hx
        exact decide_eq_true (hA_all x (mem_leftSpine_mem hx))
      simp only [restrictTree, huS, ↓reduceIte, leftSpine, hA_eq, List.filter_append, hfiltA]
      simp [hu]
    · have huS : u ∉ ({x : ℝ | x ≤ L} : Set ℝ) := hu
      have hnoB : ¬∃ b ∈ B, b ∈ ({x : ℝ | x ≤ L} : Set ℝ) := by
        rintro ⟨b, hb, hbL⟩
        exact hu (le_trans (le_of_lt (gt_of_IsBST_right A u B ht hb)) hbL)
      simp only [restrictTree, huS, hnoB, ↓reduceIte, leftSpine, List.filter_append, ihA hA_bst]
      simp [hu]

/-! ### Single Right Rotation on `leftSpine` and Folding `adjacentPairs` -/

private theorem rotateRightEdge_on_leftSpine {α : Type} [LinearOrder α]
    (B : BinaryTree α) (pre : List α) (x y : α) (rest : List α)
    (hB : B.IsBST) (hLS : leftSpine B = pre ++ (x :: y :: rest)) :
    x < y ∧
    IsSingleRotEdge B x y ∧
    rotateEdge B x y = rotateRightEdge B x y ∧
    (rotateRightEdge B x y).toKeyList = B.toKeyList ∧
    (rotateRightEdge B x y).IsBST ∧
    leftSpine (rotateRightEdge B x y) = (pre ++ [x]) ++ rest ∧
    rightSpine (rotateRightEdge B x y) =
      if rest = [] then x :: rightSpine B else rightSpine B := by
  have hsorted : (leftSpine B).Pairwise (· < ·) := leftSpine_sorted B hB
  have hxy : x < y := by
    rw [hLS, List.pairwise_append] at hsorted
    exact (List.pairwise_cons.mp hsorted.2.1).1 y List.mem_cons_self
  suffices hmain :
      IsRightRotEdge B x y ∧
      (rotateRightEdge B x y).toKeyList = B.toKeyList ∧
      leftSpine (rotateRightEdge B x y) = (pre ++ [x]) ++ rest ∧
      rightSpine (rotateRightEdge B x y) =
        if rest = [] then x :: rightSpine B else rightSpine B by
    rcases hmain with ⟨hrr, htkl, hls', hrs'⟩
    have hbst' : (rotateRightEdge B x y).IsBST := by
      rw [IsBST_iff_toKeyList_sorted, htkl, ← IsBST_iff_toKeyList_sorted]
      exact hB
    have hre : rotateEdge B x y = rotateRightEdge B x y := by
      simp [rotateEdge, hxy]
    exact ⟨hxy, Or.inl ⟨hxy, hrr⟩, hre, htkl, hbst', hls', hrs'⟩
  induction B generalizing pre rest with
  | nil =>
    simp [leftSpine] at hLS
  | node k l r ihl _ =>
    have hl_bst := IsBST_left_of_IsBST hB
    rcases List.eq_nil_or_concat rest with rfl | ⟨mid, last, hrest_eq⟩
    · have hl_eq : leftSpine l ++ [k] = (pre ++ [x]) ++ [y] := by
        simpa [leftSpine, List.append_assoc] using hLS
      obtain ⟨hl_pre, hk_eq⟩ := snoc_inj hl_eq
      subst hk_eq
      rcases l with _ | ⟨lk, ll, lr⟩
      · simp [leftSpine] at hl_pre
      · simp only [leftSpine] at hl_pre
        obtain ⟨hll_pre, hlk_eq⟩ := snoc_inj hl_pre
        subst hlk_eq
        have hrot_eq : rotateRightEdge ((ll △[lk] lr) △[k] r) lk k = ll △[lk] (lr △[k] r) := by
          simp [rotateRightEdge]
        refine ⟨?_, ?_, ?_, ?_⟩
        · refine ⟨ll, lr, r, .here, ?_⟩
          simp [subtreeAtKey]
        · rw [hrot_eq]
          simp [toKeyList, List.append_assoc]
        · rw [hrot_eq]
          simp [leftSpine, hll_pre]
        · rw [hrot_eq]
          simp [rightSpine]
    · subst hrest_eq
      have hmid_ne : mid ++ [last] ≠ [] := by simp
      have hl_eq : leftSpine l ++ [k] = (pre ++ (x :: y :: mid)) ++ [last] := by
        simpa [leftSpine, List.append_assoc] using hLS
      obtain ⟨hl_pre, hk_eq⟩ := snoc_inj hl_eq
      subst hk_eq
      have hy_in_l : y ∈ l := mem_leftSpine_mem (by rw [hl_pre]; simp)
      have hy_lt_k : y < k := lt_of_IsBST_left l k r hB hy_in_l
      have hl_sorted : (leftSpine l).Pairwise (· < ·) := leftSpine_sorted l hl_bst
      obtain ⟨⟨A, B_sub, C, hy_mem, hsub⟩, htkl_l, hls_l, _⟩ := ihl pre mid hl_bst hl_pre hl_sorted
      have hrot_eq : rotateRightEdge (l △[k] r) x y = (rotateRightEdge l x y) △[k] r := by
        simp [rotateRightEdge, hy_lt_k]
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨A, B_sub, C, .left hy_mem, ?_⟩
        simpa [subtreeAtKey, hy_lt_k] using hsub
      · rw [hrot_eq]
        simp [toKeyList, htkl_l]
      · rw [hrot_eq]
        simp [leftSpine, hls_l, List.append_assoc]
      · rw [hrot_eq]
        simp [rightSpine]

private theorem mem_of_mem_adjacentPairs {α : Type} {xs : List α} {p : α × α}
    (hp : p ∈ adjacentPairs xs) : p.1 ∈ xs ∧ p.2 ∈ xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [adjacentPairs] at hp
  | singleton a => simp [adjacentPairs] at hp
  | cons_cons a b rest ih _ =>
    simp only [adjacentPairs, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact ⟨by simp, by simp⟩
    · rcases ih hp' with ⟨h1, h2⟩
      exact ⟨by simp [h1], by simp [h2]⟩

private theorem lt_of_mem_adjacentPairs {α : Type} [LinearOrder α] {xs : List α} {p : α × α}
    (hsorted : xs.Pairwise (· < ·)) (hp : p ∈ adjacentPairs xs) : p.1 < p.2 := by
  induction xs using List.twoStepInduction with
  | nil => simp [adjacentPairs] at hp
  | singleton a => simp [adjacentPairs] at hp
  | cons_cons a b rest ih _ =>
    rw [List.pairwise_cons, List.pairwise_cons] at hsorted
    simp only [adjacentPairs, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact hsorted.1 b List.mem_cons_self
    · exact ih hsorted.2.2 hp'

private theorem fold_adjacentPairs_restrict
    (h_3_1 : Ty_lem_3_1)
    (S : Set ℝ) (hS : OrdConvex S)
    (xs : List ℝ) :
    ∀ (T : BinaryTree ℝ) (preT preB : List ℝ),
      T.IsBST →
      leftSpine T = preT ++ xs →
      leftSpine (restrictTree T S) =
        preB ++ (open Classical in xs.filter (fun x => decide (x ∈ S))) →
      let T_end := (adjacentPairs xs).foldl (fun acc p => rotateRightEdge acc p.1 p.2) T
      let pairsS := (open Classical in (adjacentPairs xs).filter
        (fun p => decide (p.1 ∈ S ∧ p.2 ∈ S)))
      let B0 := restrictTree T S
      let B_end := pairsS.foldl (fun acc p => rotateRightEdge acc p.1 p.2) B0
      T_end.IsBST ∧
      restrictTree T_end S = B_end ∧
      (leftSpine B_end).length + pairsS.length = (leftSpine B0).length ∧
      (rightSpine B_end).length ≤ (rightSpine B0).length + (if pairsS = [] then 0 else 1) ∧
      (∀ p ∈ pairsS, p.1 ∈ leftSpine B0 ∧ p.2 ∈ leftSpine B0 ∧ p.1 < p.2) := by
  classical
  induction xs using List.twoStepInduction with
  | nil =>
    intro T preT preB hT _ _
    simp [adjacentPairs, hT]
  | singleton a =>
    intro T preT preB hT _ _
    simp [adjacentPairs, hT]
  | cons_cons x y xs' ih _ =>
    intro T preT preB hT hLST hLSB
    have hsortedT : (leftSpine T).Pairwise (· < ·) := leftSpine_sorted T hT
    have hsorted_xs : (x :: y :: xs').Pairwise (· < ·) := by
      rw [hLST, List.pairwise_append] at hsortedT
      exact hsortedT.2.1
    have hB0_bst : (restrictTree T S).IsBST :=
      (h_3_1 T S hT (isLCAClosed_of_ordConvex hS T)).1.1
    have hpairs_props : ∀ p ∈ (adjacentPairs (x :: y :: xs')).filter
        (fun p => decide (p.1 ∈ S ∧ p.2 ∈ S)),
        p.1 ∈ leftSpine (restrictTree T S) ∧
        p.2 ∈ leftSpine (restrictTree T S) ∧ p.1 < p.2 := by
      intro p hp
      rw [List.mem_filter] at hp
      rcases hp with ⟨hp_adj, hp_S⟩
      simp only [decide_eq_true_eq] at hp_S
      rcases mem_of_mem_adjacentPairs hp_adj with ⟨hp1_xs, hp2_xs⟩
      have hp1_f : p.1 ∈ (x :: y :: xs').filter (fun u => decide (u ∈ S)) :=
        List.mem_filter.mpr ⟨hp1_xs, decide_eq_true hp_S.1⟩
      have hp2_f : p.2 ∈ (x :: y :: xs').filter (fun u => decide (u ∈ S)) :=
        List.mem_filter.mpr ⟨hp2_xs, decide_eq_true hp_S.2⟩
      rw [hLSB]
      exact ⟨List.mem_append_right preB hp1_f, List.mem_append_right preB hp2_f,
        lt_of_mem_adjacentPairs hsorted_xs hp_adj⟩
    obtain ⟨hxy, hrotT, hreT, _, hT1_bst, hLST1, _⟩ :=
      rotateRightEdge_on_leftSpine T preT x y xs' hT hLST
    let T1 := rotateRightEdge T x y
    have h31_rot := (h_3_1 T S hT (isLCAClosed_of_ordConvex hS T)).2.1 x y hrotT
      (by rw [hreT]; exact isLCAClosed_of_ordConvex hS T1)
    rw [hreT] at h31_rot
    by_cases hxS : x ∈ S
    · by_cases hyS : y ∈ S
      · -- Both x ∈ S and y ∈ S
        have hboth : x ∈ S ∧ y ∈ S := ⟨hxS, hyS⟩
        have hLSB_xy : leftSpine (restrictTree T S) =
            preB ++ (x :: y :: xs'.filter (fun u => decide (u ∈ S))) := by
          simpa [hxS, hyS] using hLSB
        obtain ⟨_, _, hreB, _, _, hLSB1, hRSB1⟩ :=
          rotateRightEdge_on_leftSpine (restrictTree T S) preB x y
            (xs'.filter (fun u => decide (u ∈ S))) hB0_bst hLSB_xy
        have hRT1_eq : restrictTree T1 S = rotateRightEdge (restrictTree T S) x y := by
          rw [(h31_rot.1 hboth).2, hreB]
        have hLSB1' : leftSpine (restrictTree T1 S) =
            (preB ++ [x]) ++ xs'.filter (fun u => decide (u ∈ S)) := by
          rw [hRT1_eq]; exact hLSB1
        obtain ⟨hTend_bst, hRTend, hLS_len', hRS_len', _⟩ :=
          ih T1 (preT ++ [x]) (preB ++ [x]) hT1_bst hLST1 hLSB1'
        have hLSB0_B1 : (leftSpine (restrictTree T1 S)).length + 1 =
            (leftSpine (restrictTree T S)).length := by
          rw [hLSB1', hLSB_xy]
          simp [List.length_append]
          omega
        refine ⟨hTend_bst, ?_, ?_, ?_, hpairs_props⟩
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hRTend
        · dsimp only [adjacentPairs]
          simp only [List.filter_cons, hxS, hyS, and_self, decide_true, ↓reduceIte,
            List.length_cons, List.foldl_cons]
          rw [← hRT1_eq]
          omega
        · dsimp only [adjacentPairs]
          simp only [List.filter_cons, hxS, hyS, and_self, decide_true, ↓reduceIte,
            List.foldl_cons, reduceCtorEq]
          rw [← hRT1_eq]
          by_cases hfilt_nil : xs'.filter (fun u => decide (u ∈ S)) = []
          · have hpairs'_nil :
                (adjacentPairs xs').filter (fun p => decide (p.1 ∈ S ∧ p.2 ∈ S)) = [] := by
              rw [List.filter_eq_nil_iff]
              intro p hp
              simp only [decide_eq_true_eq, not_and]
              intro hp1S _
              have hp1_xs' := (mem_of_mem_adjacentPairs hp).1
              have hp1_in : p.1 ∈ xs'.filter (fun u => decide (u ∈ S)) :=
                List.mem_filter.mpr ⟨hp1_xs', decide_eq_true hp1S⟩
              rw [hfilt_nil] at hp1_in
              simp at hp1_in
            rw [hpairs'_nil, List.foldl_nil, hRT1_eq, hRSB1]
            simp [hfilt_nil]
          · have hRSB1_eq : rightSpine (restrictTree T1 S) = rightSpine (restrictTree T S) := by
              rw [hRT1_eq, hRSB1]
              simp [hfilt_nil]
            have := hRS_len'
            rw [hRSB1_eq] at this
            split at this <;> omega
      · -- x ∈ S and y ∉ S
        have hnboth : ¬(x ∈ S ∧ y ∈ S) := fun h => hyS h.2
        have hRT1_eq : restrictTree T1 S = restrictTree T S := h31_rot.2 hnboth
        have hfilt_nil : xs'.filter (fun u => decide (u ∈ S)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz
          simp only [decide_eq_true_eq]
          intro hzS
          rw [List.pairwise_cons, List.pairwise_cons] at hsorted_xs
          have hyz : y < z := hsorted_xs.2.1 z hz
          exact hyS (hS (le_of_lt hxy) (le_of_lt hyz) hxS hzS)
        have hLSB1 : leftSpine (restrictTree T1 S) =
            (preB ++ [x]) ++ xs'.filter (fun u => decide (u ∈ S)) := by
          rw [hRT1_eq, hLSB]
          simp [hxS, hyS, hfilt_nil]
        obtain ⟨hTend_bst, hRTend, hLS_len', hRS_len', _⟩ :=
          ih T1 (preT ++ [x]) (preB ++ [x]) hT1_bst hLST1 hLSB1
        refine ⟨hTend_bst, ?_, ?_, ?_, hpairs_props⟩
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hRTend
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hLS_len'
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hRS_len'
    · -- x ∉ S
      have hnboth : ¬(x ∈ S ∧ y ∈ S) := fun h => hxS h.1
      have hRT1_eq : restrictTree T1 S = restrictTree T S := h31_rot.2 hnboth
      by_cases hyS : y ∈ S
      · have hLSB1 : leftSpine (restrictTree T1 S) =
            (preB ++ [y]) ++ xs'.filter (fun u => decide (u ∈ S)) := by
          rw [hRT1_eq, hLSB]
          simp [hxS, hyS, List.append_assoc]
        obtain ⟨hTend_bst, hRTend, hLS_len', hRS_len', _⟩ :=
          ih T1 (preT ++ [x]) (preB ++ [y]) hT1_bst hLST1 hLSB1
        refine ⟨hTend_bst, ?_, ?_, ?_, hpairs_props⟩
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hRTend
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hLS_len'
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hRS_len'
      · have hLSB1 : leftSpine (restrictTree T1 S) =
            preB ++ xs'.filter (fun u => decide (u ∈ S)) := by
          rw [hRT1_eq, hLSB]
          simp [hxS, hyS]
        obtain ⟨hTend_bst, hRTend, hLS_len', hRS_len', _⟩ :=
          ih T1 (preT ++ [x]) preB hT1_bst hLST1 hLSB1
        refine ⟨hTend_bst, ?_, ?_, ?_, hpairs_props⟩
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hRTend
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hLS_len'
        · simpa [adjacentPairs, hxS, hyS, T1, hRT1_eq] using hRS_len'

/-! ### Straddling Pairs Bound -/

private noncomputable def zoneCode (Lm Rm x : ℝ) : ℕ :=
  open Classical in
  if x ≤ Lm then 0 else if x < Rm then 1 else 2

private theorem zoneCode_le_two (Lm Rm x : ℝ) : zoneCode Lm Rm x ≤ 2 := by
  classical
  unfold zoneCode
  split_ifs <;> omega

private theorem zoneCode_mono {Lm Rm x y : ℝ} (_hLmRm : Lm < Rm) (hxy : x ≤ y) :
    zoneCode Lm Rm x ≤ zoneCode Lm Rm y := by
  classical
  unfold zoneCode
  split_ifs <;> linarith

private theorem straddle_bound_aux {Lm Rm : ℝ} (hLmRm : Lm < Rm) :
    ∀ (xs : List ℝ) (b : ℕ),
      xs.Pairwise (· < ·) →
      (∀ x ∈ xs, b ≤ zoneCode Lm Rm x) →
      (adjacentPairs xs).length ≤
        (open Classical in
          ((adjacentPairs xs).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm))).length +
          ((adjacentPairs xs).filter
            (fun p => decide ((Lm < p.1 ∧ p.1 < Rm) ∧ (Lm < p.2 ∧ p.2 < Rm)))).length +
          ((adjacentPairs xs).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2))).length) +
        (2 - b) := by
  classical
  intro xs
  induction xs using List.twoStepInduction with
  | nil => intro b _ _; simp [adjacentPairs]
  | singleton a => intro b _ _; simp [adjacentPairs]
  | cons_cons x y xs' ih _ =>
    intro b hsorted hb
    rw [List.pairwise_cons, List.pairwise_cons] at hsorted
    have hxy : x < y := hsorted.1 y List.mem_cons_self
    have hbx : b ≤ zoneCode Lm Rm x := hb x List.mem_cons_self
    have hxy_z : zoneCode Lm Rm x ≤ zoneCode Lm Rm y := zoneCode_mono hLmRm (le_of_lt hxy)
    have hy2 : zoneCode Lm Rm y ≤ 2 := zoneCode_le_two Lm Rm y
    have hb' : ∀ z ∈ xs', zoneCode Lm Rm y ≤ zoneCode Lm Rm z :=
      fun z hz => zoneCode_mono hLmRm (le_of_lt (hsorted.2.1 z hz))
    have hrec := ih (zoneCode Lm Rm y) hsorted.2.2 hb'
    dsimp only [adjacentPairs]
    simp only [List.length_cons, List.filter_cons]
    by_cases hsame : zoneCode Lm Rm x = zoneCode Lm Rm y
    · rcases hzx : zoneCode Lm Rm x with _ | _ | _ | k
      · have hxL : x ≤ Lm := by
          unfold zoneCode at hzx; split_ifs at hzx with h1; exact h1
        have hyL : y ≤ Lm := by
          have hzy : zoneCode Lm Rm y = 0 := by omega
          unfold zoneCode at hzy; split_ifs at hzy with h1; exact h1
        have hnotM : ¬((Lm < x ∧ x < Rm) ∧ (Lm < y ∧ y < Rm)) :=
          fun h => not_lt_of_ge hxL h.1.1
        have hnotR : ¬(Rm ≤ x ∧ Rm ≤ y) :=
          fun h => not_lt_of_ge (le_trans h.1 hxL) hLmRm
        simp only [hxL, hyL, and_self, hnotM, hnotR, decide_true, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]
        omega
      · have hxM : Lm < x ∧ x < Rm := by
          unfold zoneCode at hzx
          split_ifs at hzx with h1 h2 <;> first | exact ⟨lt_of_not_ge h1, h2⟩ | omega
        have hyM : Lm < y ∧ y < Rm := by
          have hzy : zoneCode Lm Rm y = 1 := by omega
          unfold zoneCode at hzy
          split_ifs at hzy with h1 h2 <;> first | exact ⟨lt_of_not_ge h1, h2⟩ | omega
        have hnotL : ¬(x ≤ Lm ∧ y ≤ Lm) := fun h => not_lt_of_ge h.1 hxM.1
        have hnotR : ¬(Rm ≤ x ∧ Rm ≤ y) := fun h => not_lt_of_ge h.1 hxM.2
        simp only [hxM, hyM, and_self, hnotL, hnotR, decide_true, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]
        omega
      · have hxR : Rm ≤ x := by
          unfold zoneCode at hzx
          split_ifs at hzx with h1 h2 <;> first | exact le_of_not_gt h2 | omega
        have hyR : Rm ≤ y := le_trans hxR (le_of_lt hxy)
        have hnotL : ¬(x ≤ Lm ∧ y ≤ Lm) :=
          fun h => not_lt_of_ge (le_trans hxR h.1) hLmRm
        have hnotM : ¬((Lm < x ∧ x < Rm) ∧ (Lm < y ∧ y < Rm)) :=
          fun h => not_lt_of_ge hxR h.1.2
        simp only [hxR, hyR, and_self, hnotL, hnotM, decide_true, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]
        omega
      · have := zoneCode_le_two Lm Rm x
        omega
    · have hnotL : ¬(x ≤ Lm ∧ y ≤ Lm) := by
        rintro ⟨hxL, hyL⟩
        apply hsame
        unfold zoneCode
        simp [hxL, hyL]
      have hnotM : ¬((Lm < x ∧ x < Rm) ∧ (Lm < y ∧ y < Rm)) := by
        rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2'⟩⟩
        apply hsame
        have hnx : ¬(x ≤ Lm) := not_le_of_gt hx1
        have hny : ¬(y ≤ Lm) := not_le_of_gt hy1
        unfold zoneCode
        simp [hnx, hx2, hny, hy2']
      have hnotR : ¬(Rm ≤ x ∧ Rm ≤ y) := by
        rintro ⟨hxR, hyR⟩
        apply hsame
        have hnx1 : ¬(x ≤ Lm) := not_le_of_gt (lt_of_lt_of_le hLmRm hxR)
        have hnx2 : ¬(x < Rm) := not_lt_of_ge hxR
        have hny1 : ¬(y ≤ Lm) := not_le_of_gt (lt_of_lt_of_le hLmRm hyR)
        have hny2 : ¬(y < Rm) := not_lt_of_ge hyR
        unfold zoneCode
        simp [hnx1, hnx2, hny1, hny2]
      simp only [hnotL, hnotM, hnotR, decide_false, Bool.false_eq_true, ↓reduceIte]
      omega

/-! ### `negMirror` Duality on `BinaryTree ℝ` -/

private def negMirror (t : BinaryTree ℝ) : BinaryTree ℝ :=
  (t.map (- ·)).mirror

private theorem negMirror_involutive (t : BinaryTree ℝ) :
    negMirror (negMirror t) = t := by
  unfold negMirror
  rw [mirror_map, mirror_mirror, map_map]
  have hcomp : ((- · : ℝ → ℝ) ∘ (- ·)) = fun x => x := by
    funext x; exact neg_neg x
  rw [hcomp, map_id']

private theorem negMirror_eq_nil_iff (t : BinaryTree ℝ) :
    negMirror t = .nil ↔ t = .nil := by
  cases t <;> simp [negMirror, BinaryTree.map]

private theorem negMirror_isBST (t : BinaryTree ℝ) (ht : t.IsBST) :
    (negMirror t).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at ht ⊢
  unfold negMirror
  rw [toKeyList_mirror, toKeyList_map, List.pairwise_reverse, List.pairwise_map]
  exact ht.imp (fun {a b} hab => neg_lt_neg hab)

private theorem leftSpine_negMirror (t : BinaryTree ℝ) :
    leftSpine (negMirror t) = (rightSpineBottomUp t).map (- ·) := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    simp only [negMirror, BinaryTree.map, mirror, leftSpine, rightSpineBottomUp, rightSpine,
      List.reverse_cons, List.map_append, List.map_singleton]
    congr 1

private theorem rightSpine_negMirror (t : BinaryTree ℝ) :
    rightSpine (negMirror t) = (leftSpine t).reverse.map (- ·) := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    simp only [negMirror, BinaryTree.map, mirror, rightSpine, leftSpine,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
    congr 1

private theorem minKey?_negMirror (t : BinaryTree ℝ) :
    (negMirror t).minKey? = t.maxKey?.map (- ·) := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    have hn : negMirror (l △[k] r) = (negMirror r) △[-k] (negMirror l) := rfl
    rw [hn]
    simp only [BinaryTree.minKey?, BinaryTree.maxKey?, ihr]
    cases r.maxKey? <;> rfl

private theorem spliceMin_negMirror (t : BinaryTree ℝ) :
    spliceMin (negMirror t) = negMirror (spliceMax t) := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    rcases r with _ | ⟨rk, rl, rr⟩
    · rfl
    · have hr_eq : negMirror (rl △[rk] rr) = (negMirror rr) △[-rk] (negMirror rl) := rfl
      change spliceMin ((negMirror (rl △[rk] rr)) △[-k] (negMirror l)) =
        (negMirror (spliceMax (rl △[rk] rr))) △[-k] (negMirror l)
      rw [← ihr, hr_eq]
      rfl

private theorem rotateRightEdge_negMirror (t : BinaryTree ℝ) (x p : ℝ) :
    rotateRightEdge (negMirror t) (-x) (-p) = negMirror (rotateLeftEdge t x p) := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    change rotateRightEdge ((negMirror r) △[-k] (negMirror l)) (-x) (-p) =
      negMirror (rotateLeftEdge (l △[k] r) x p)
    by_cases hpk : p < k
    · have hnp : -k < -p := neg_lt_neg hpk
      have hnot : ¬(-p < -k) := not_lt_of_gt hnp
      simp only [rotateRightEdge, rotateLeftEdge, hpk, hnp, hnot, ↓reduceIte]
      change (negMirror r) △[-k] (rotateRightEdge (negMirror l) (-x) (-p)) =
        (negMirror r) △[-k] (negMirror (rotateLeftEdge l x p))
      rw [ihl]
    · by_cases hkp : k < p
      · have hnp : -p < -k := neg_lt_neg hkp
        simp only [rotateRightEdge, rotateLeftEdge, hpk, hkp, hnp, ↓reduceIte]
        change (rotateRightEdge (negMirror r) (-x) (-p)) △[-k] (negMirror l) =
          (negMirror (rotateLeftEdge r x p)) △[-k] (negMirror l)
        rw [ihr]
      · have hp_eq : p = k := le_antisymm (not_lt.mp hkp) (not_lt.mp hpk)
        subst hp_eq
        simp only [rotateRightEdge, rotateLeftEdge, lt_irrefl, ↓reduceIte]
        rcases r with _ | ⟨rx, rb, rc⟩
        · rfl
        · change (if -rx = -x then (negMirror rc) △[-rx] ((negMirror rb) △[-p] (negMirror l))
            else ((negMirror rc) △[-rx] (negMirror rb)) △[-p] (negMirror l)) =
            negMirror (if rx = x then (l △[p] rb) △[rx] rc else l △[p] (rb △[rx] rc))
          by_cases hrx : rx = x
          · subst hrx; simp [negMirror, BinaryTree.map, mirror]
          · have hnrx : -rx ≠ -x := fun h => hrx (neg_inj.mp h)
            simp [hrx, hnrx, negMirror, BinaryTree.map, mirror]

private theorem adjacentPairs_map {α β : Type} (f : α → β) (xs : List α) :
    adjacentPairs (xs.map f) = (adjacentPairs xs).map (fun p => (f p.1, f p.2)) := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rest ih _ =>
    simp [adjacentPairs, ih]

private theorem popCascadePairs_negMirror (t : BinaryTree ℝ) :
    popCascadePairs (negMirror t) = (ejectCascadePairs t).map (fun p => (-p.1, -p.2)) := by
  unfold popCascadePairs ejectCascadePairs
  rw [leftSpine_negMirror, ← List.map_tail, adjacentPairs_map]

private theorem popCascade_negMirror (t : BinaryTree ℝ) :
    popCascade (negMirror t) = negMirror (ejectCascade t) := by
  unfold popCascade ejectCascade
  rw [popCascadePairs_negMirror, spliceMin_negMirror, List.foldl_map]
  suffices h : ∀ (ps : List (ℝ × ℝ)) (acc : BinaryTree ℝ),
      ps.foldl (fun a p => rotateRightEdge a (-p.1) (-p.2)) (negMirror acc) =
        negMirror (ps.foldl (fun a p => rotateLeftEdge a p.1 p.2) acc) from
    h (ejectCascadePairs t) (spliceMax t)
  intro ps
  induction ps with
  | nil => intro acc; rfl
  | cons p rest ih =>
    intro acc
    simp only [List.foldl_cons, rotateRightEdge_negMirror]
    exact ih (rotateLeftEdge acc p.1 p.2)

private theorem mem_negMirror_iff (t : BinaryTree ℝ) (y : ℝ) :
    y ∈ negMirror t ↔ -y ∈ t := by
  unfold negMirror
  rw [mem_mirror_iff, mem_map_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨-y, h, neg_neg y⟩

private theorem restrictTree_negMirror (t : BinaryTree ℝ) (S : Set ℝ)
    (ht : t.IsBST) (hS : OrdConvex S) :
    restrictTree (negMirror t) {y : ℝ | -y ∈ S} = negMirror (restrictTree t S) := by
  classical
  induction t with
  | nil => rfl
  | node u A B ihA ihB =>
    have hA_bst := IsBST_left_of_IsBST ht
    have hB_bst := IsBST_right_of_IsBST ht
    change restrictTree ((negMirror B) △[-u] (negMirror A)) {y : ℝ | -y ∈ S} =
      negMirror (restrictTree (u |> fun u => A △[u] B) S)
    by_cases hu : u ∈ S
    · have hnu : -u ∈ ({y : ℝ | -y ∈ S} : Set ℝ) := by simp [hu]
      simp only [restrictTree, hu, hnu, ↓reduceIte]
      rw [ihB hB_bst, ihA hA_bst]
      rfl
    · have hnu : -u ∉ ({y : ℝ | -y ∈ S} : Set ℝ) := by simp [hu]
      have hexA_iff : (∃ y ∈ negMirror A, y ∈ ({y : ℝ | -y ∈ S} : Set ℝ)) ↔ ∃ a ∈ A, a ∈ S := by
        constructor
        · rintro ⟨y, hy, hyS⟩
          exact ⟨-y, (mem_negMirror_iff A y).mp hy, hyS⟩
        · rintro ⟨a, ha, haS⟩
          exact ⟨-a, (mem_negMirror_iff A (-a)).mpr (by simpa using ha), by simpa using haS⟩
      by_cases hB : ∃ b ∈ B, b ∈ S
      · have hnoA : ¬∃ a ∈ A, a ∈ S := by
          rintro ⟨a, ha, haS⟩
          rcases hB with ⟨b, hb, hbS⟩
          have hau : a ≤ u := le_of_lt (lt_of_IsBST_left A u B ht ha)
          have hub : u ≤ b := le_of_lt (gt_of_IsBST_right A u B ht hb)
          exact hu (hS hau hub haS hbS)
        have hnoA' : ¬∃ y ∈ negMirror A, y ∈ ({y : ℝ | -y ∈ S} : Set ℝ) :=
          mt hexA_iff.mp hnoA
        simp only [restrictTree, hu, hnu, hB, hnoA', ↓reduceIte]
        exact ihB hB_bst
      · by_cases hA : ∃ a ∈ A, a ∈ S
        · have hA' : ∃ y ∈ negMirror A, y ∈ ({y : ℝ | -y ∈ S} : Set ℝ) := hexA_iff.mpr hA
          simp only [restrictTree, hu, hnu, hB, hA', ↓reduceIte]
          exact ihA hA_bst
        · have hnoA' : ¬∃ y ∈ negMirror A, y ∈ ({y : ℝ | -y ∈ S} : Set ℝ) :=
            mt hexA_iff.mp hA
          simp only [restrictTree, hu, hnu, hB, hnoA', ↓reduceIte]
          rw [ihB hB_bst, restrictTree_eq_nil_of_disjoint B S (fun b hb hbS => hB ⟨b, hb, hbS⟩),
            restrictTree_eq_nil_of_disjoint A S (fun a ha haS => hA ⟨a, ha, haS⟩)]

/-! ### Single-Step `POP` and `EJECT` Spine Potential Lemmas -/

private noncomputable def spinePot (Lm Rm : ℝ) (T : BinaryTree ℝ) : ℕ :=
  let U := restrictTree T {x : ℝ | x ≤ Lm}
  let M := restrictTree T {x : ℝ | Lm < x ∧ x < Rm}
  let W := restrictTree T {x : ℝ | Rm ≤ x}
  (leftSpine M).length + (rightSpine M).length + (rightSpine U).length + (leftSpine W).length

private theorem pop_step_accounting
    (h_3_1 : Ty_lem_3_1) (h_3_2 : Ty_lem_3_2)
    {Lm Rm : ℝ} (hLmRm : Lm < Rm)
    (T : BinaryTree ℝ) (hT : T.IsBST) (hne : T ≠ .nil)
    (hminL : ∀ xMin : ℝ, T.minKey? = some xMin → xMin ≤ Lm) :
    let T' := SplayTree.pop T
    let U := restrictTree T {x : ℝ | x ≤ Lm}
    let U' := restrictTree T' {x : ℝ | x ≤ Lm}
    let W := restrictTree T {x : ℝ | Rm ≤ x}
    let W' := restrictTree T' {x : ℝ | Rm ≤ x}
    let pairsL := (open Classical in
      (popCascadePairs T).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm)))
    let pairsR := (open Classical in
      (popCascadePairs T).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2)))
    popCost T + 2 * (spinePot Lm Rm T' : ℝ) ≤
      2 * (pairsL.length : ℝ) + 2 * (spinePot Lm Rm T : ℝ) + 9 ∧
    U ≠ .nil ∧
    (rightSpine U').length ≤ (rightSpine U).length + 1 ∧
    (leftSpine W').length + pairsR.length = (leftSpine W).length ∧
    (∀ p ∈ pairsR, p.1 ∈ leftSpine W ∧ p.2 ∈ leftSpine W ∧ p.1 < p.2) ∧
    W' = pairsR.foldl (fun acc p => rotateRightEdge acc p.1 p.2) W := by
  classical
  obtain ⟨xMin, hxMin, hxMin_mem, _, _, _, _, _, _, _⟩ := pop_spec_poly T hT hne
  have hxMinL : xMin ≤ Lm := hminL xMin hxMin
  obtain ⟨⟨_, hk_div, hpairs_len, hcost_eq, hpop_eq⟩, _⟩ := (h_3_2 T hT hne)
  let xs := (leftSpine T).tail
  have hxs_sorted : xs.Pairwise (· < ·) := by
    have hls := leftSpine_sorted T hT
    cases h : leftSpine T with
    | nil => exact absurd ((leftSpine_eq_nil_iff T).mp h) hne
    | cons a as =>
      rw [h] at hls
      simpa [xs, h] using (List.pairwise_cons.mp hls).2
  have hTmin_bst : (spliceMin T).IsBST := isBST_spliceMin T hT
  rcases leftSpine_spliceMin_suffix T with ⟨preT, hLSTmin⟩
  -- 1. Projection onto IL = {x | x ≤ Lm}
  let IL : Set ℝ := {x : ℝ | x ≤ Lm}
  have h31_L := h_3_1 T IL hT (isLCAClosed_of_ordConvex (ordConvex_Iic Lm) T)
  have hU_ne : restrictTree T IL ≠ .nil := by
    have hxU : xMin ∈ restrictTree T IL := (h31_L.1.2 xMin).mpr ⟨hxMin_mem, hxMinL⟩
    exact ne_nil_of_mem xMin hxU
  have hsplice_L : restrictTree (spliceMin T) IL = spliceMin (restrictTree T IL) :=
    ((h31_L.2.2 hne).1.2 xMin hxMin).1 hxMinL |>.2
  have hLS_U : leftSpine (restrictTree T IL) =
      (leftSpine T).filter (fun x => decide (x ≤ Lm)) :=
    leftSpine_restrictTree_Iic T Lm hT
  have hLS_T_cons : leftSpine T = xMin :: xs := by
    cases h : leftSpine T with
    | nil => exact absurd ((leftSpine_eq_nil_iff T).mp h) hne
    | cons a as =>
      have ha_min : T.minKey? = some a := by
        clear * - h
        induction T generalizing a as with
        | nil => simp [leftSpine] at h
        | node k l r ihl _ =>
          simp only [leftSpine] at h
          cases hl : leftSpine l with
          | nil =>
            have hl_nil : l = .nil := (leftSpine_eq_nil_iff l).mp hl
            subst hl_nil
            simp only [leftSpine, List.nil_append, List.cons.injEq] at h
            rcases h with ⟨rfl, _⟩
            rfl
          | cons b bs =>
            rw [hl, List.cons_append, List.cons.injEq] at h
            rcases h with ⟨rfl, _⟩
            have hmin_l := ihl b bs hl
            simp [BinaryTree.minKey?, hmin_l]
      rw [hxMin] at ha_min
      rcases Option.some.inj ha_min with rfl
      dsimp only [xs]
      rw [h]
      rfl
  have hfilt_eq_IL : ∀ l : List ℝ,
      l.filter (fun x => decide (x ∈ IL)) = l.filter (fun x => decide (x ≤ Lm)) :=
    fun l => List.filter_congr (fun x _ => by simp [IL])
  have hLS_U_tail : (leftSpine (restrictTree T IL)).tail =
      xs.filter (fun x => decide (x ∈ IL)) := by
    rw [hfilt_eq_IL, hLS_U, hLS_T_cons]
    simp [hxMinL]
  rcases leftSpine_spliceMin_suffix (restrictTree T IL) with ⟨preUL, hLS_Usplice⟩
  rw [hLS_U_tail, ← hsplice_L] at hLS_Usplice
  obtain ⟨_, hRTend_L, _, hRS_U_end, _⟩ :=
    fold_adjacentPairs_restrict h_3_1 IL (ordConvex_Iic Lm) xs (spliceMin T) preT preUL
      hTmin_bst hLSTmin hLS_Usplice
  have hRS_U_bound :
      (rightSpine (restrictTree (SplayTree.pop T) IL)).length ≤
        (rightSpine (restrictTree T IL)).length + 1 := by
    rw [hpop_eq]
    change (rightSpine (restrictTree ((adjacentPairs xs).foldl _ (spliceMin T)) IL)).length ≤ _
    rw [hRTend_L]
    by_cases hxsL_nil : xs.filter (fun x => decide (x ≤ Lm)) = []
    · have hpairsL_nil :
          (adjacentPairs xs).filter (fun p => decide (p.1 ∈ IL ∧ p.2 ∈ IL)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        simp only [decide_eq_true_eq, not_and]
        intro hp1L _
        have hp1_le : p.1 ≤ Lm := hp1L
        have hp1_in : p.1 ∈ xs.filter (fun x => decide (x ≤ Lm)) :=
          List.mem_filter.mpr ⟨(mem_of_mem_adjacentPairs hp).1, decide_eq_true hp1_le⟩
        rw [hxsL_nil] at hp1_in; simp at hp1_in
      rw [hpairsL_nil, List.foldl_nil, hsplice_L]
      have hLS_U_one : leftSpine (restrictTree T IL) = [xMin] := by
        rw [hLS_U, hLS_T_cons]
        simp [hxMinL, hxsL_nil]
      rcases hU_cases : restrictTree T IL with _ | ⟨uk, ul, ur⟩
      · exact absurd hU_cases hU_ne
      · rw [hU_cases] at hLS_U_one
        have hul_nil : ul = .nil := by
          cases ul with
          | nil => rfl
          | node a b c =>
            simp only [leftSpine, List.append_assoc, List.singleton_append] at hLS_U_one
            cases hls_b : leftSpine b <;> simp [hls_b] at hLS_U_one
        subst hul_nil
        simp only [spliceMin, rightSpine, List.length_cons]
        omega
    · have hlen2 : 2 ≤ (leftSpine (restrictTree T IL)).length := by
        rw [hLS_U, hLS_T_cons]
        simp only [List.filter_cons, hxMinL, decide_true, ↓reduceIte, List.length_cons]
        have hpos : 0 < (xs.filter (fun x => decide (x ≤ Lm))).length :=
          List.length_pos_iff_ne_nil.mpr hxsL_nil
        omega
      have hrs_eq : rightSpine (restrictTree (spliceMin T) IL) = rightSpine (restrictTree T IL) := by
        rw [hsplice_L]
        exact rightSpine_spliceMin_of_two _ hlen2
      have h := hRS_U_end
      rw [hrs_eq] at h
      split at h <;> omega
  -- 2. Projection onto IM = {x | Lm < x ∧ x < Rm}
  let IM : Set ℝ := {x : ℝ | Lm < x ∧ x < Rm}
  have h31_M := h_3_1 T IM hT (isLCAClosed_of_ordConvex (ordConvex_Ioo Lm Rm) T)
  have hxMin_notM : xMin ∉ IM := fun h => not_lt_of_ge hxMinL h.1
  have hsplice_M : restrictTree (spliceMin T) IM = restrictTree T IM :=
    ((h31_M.2.2 hne).1.2 xMin hxMin).2 hxMin_notM
  rcases leftSpine_restrictTree_suffix T IM hT (ordConvex_Ioo Lm Rm) with ⟨preM, hLS_M⟩
  have hLS_M_xs : leftSpine (restrictTree (spliceMin T) IM) =
      preM ++ xs.filter (fun x => @decide (x ∈ IM) (Classical.propDecidable _)) := by
    rw [hsplice_M, hLS_M, hLS_T_cons]
    simp only [List.filter_cons, hxMin_notM, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨_, hRTend_M, hLS_M_end, hRS_M_end, _⟩ :=
    fold_adjacentPairs_restrict h_3_1 IM (ordConvex_Ioo Lm Rm) xs (spliceMin T) preT preM
      hTmin_bst hLSTmin hLS_M_xs
  -- 3. Projection onto IR = {x | Rm ≤ x}
  let IR : Set ℝ := {x : ℝ | Rm ≤ x}
  have h31_R := h_3_1 T IR hT (isLCAClosed_of_ordConvex (ordConvex_Ici Rm) T)
  have hxMin_notR : xMin ∉ IR := not_le_of_gt (lt_of_le_of_lt hxMinL hLmRm)
  have hsplice_R : restrictTree (spliceMin T) IR = restrictTree T IR :=
    ((h31_R.2.2 hne).1.2 xMin hxMin).2 hxMin_notR
  rcases leftSpine_restrictTree_suffix T IR hT (ordConvex_Ici Rm) with ⟨preR, hLS_R⟩
  have hLS_R_xs : leftSpine (restrictTree (spliceMin T) IR) =
      preR ++ xs.filter (fun x => @decide (x ∈ IR) (Classical.propDecidable _)) := by
    rw [hsplice_R, hLS_R, hLS_T_cons]
    simp only [List.filter_cons, hxMin_notR, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨_, hRTend_R, hLS_R_end, _, hpairsR_props⟩ :=
    fold_adjacentPairs_restrict h_3_1 IR (ordConvex_Ici Rm) xs (spliceMin T) preT preR
      hTmin_bst hLSTmin hLS_R_xs
  -- 4. Combine straddle bound and potential changes
  have hpairsR_eq :
      (adjacentPairs xs).filter (fun p => decide (p.1 ∈ IR ∧ p.2 ∈ IR)) =
        (adjacentPairs xs).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2)) :=
    List.filter_congr (fun p _ => by simp [IR])
  have hstraddle' :
      (adjacentPairs xs).length ≤
        ((adjacentPairs xs).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm))).length +
          ((adjacentPairs xs).filter
            (fun p => decide ((Lm < p.1 ∧ p.1 < Rm) ∧ (Lm < p.2 ∧ p.2 < Rm)))).length +
          ((adjacentPairs xs).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2))).length + 2 :=
    straddle_bound_aux hLmRm xs 0 hxs_sorted (fun _ _ => Nat.zero_le _)
  have hW_eq' : restrictTree (SplayTree.pop T) IR =
      ((adjacentPairs xs).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2))).foldl
        (fun acc p => rotateRightEdge acc p.1 p.2) (restrictTree T IR) := by
    rw [hpop_eq]
    change restrictTree ((adjacentPairs xs).foldl _ (spliceMin T)) IR = _
    rw [hRTend_R, hsplice_R, hpairsR_eq]
  have hM_ls_bound :
      (leftSpine (restrictTree (SplayTree.pop T) IM)).length +
        ((adjacentPairs xs).filter
          (fun p => decide ((Lm < p.1 ∧ p.1 < Rm) ∧ (Lm < p.2 ∧ p.2 < Rm)))).length =
        (leftSpine (restrictTree T IM)).length := by
    rw [hpop_eq]
    change (leftSpine (restrictTree ((adjacentPairs xs).foldl _ (spliceMin T)) IM)).length + _ = _
    rw [hRTend_M, hsplice_M]
    have hlen_eq :
        ((adjacentPairs xs).filter
          (fun p => decide ((Lm < p.1 ∧ p.1 < Rm) ∧ (Lm < p.2 ∧ p.2 < Rm)))).length =
        ((adjacentPairs xs).filter
          (fun p => @decide (p.1 ∈ IM ∧ p.2 ∈ IM)
            (@instDecidableAnd _ _ (Classical.propDecidable _) (Classical.propDecidable _)))).length :=
      congrArg List.length (List.filter_congr (fun p _ => by simp [IM]))
    rw [hlen_eq]
    have h := hLS_M_end
    rwa [hsplice_M] at h
  have hM_rs_bound :
      (rightSpine (restrictTree (SplayTree.pop T) IM)).length ≤
        (rightSpine (restrictTree T IM)).length + 1 := by
    rw [hpop_eq]
    change (rightSpine (restrictTree ((adjacentPairs xs).foldl _ (spliceMin T)) IM)).length ≤ _
    rw [hRTend_M, hsplice_M]
    have h := hRS_M_end
    rw [hsplice_M] at h
    split at h <;> omega
  have hW_ls_bound :
      (leftSpine (restrictTree (SplayTree.pop T) IR)).length +
        ((adjacentPairs xs).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2))).length =
        (leftSpine (restrictTree T IR)).length := by
    rw [hW_eq', ← hpairsR_eq]
    have h := hLS_R_end
    rwa [hsplice_R] at h
  have hr_pot_nat :
      (adjacentPairs xs).length + spinePot Lm Rm (SplayTree.pop T) ≤
        ((adjacentPairs xs).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm))).length +
          spinePot Lm Rm T + 4 := by
    unfold spinePot
    change (adjacentPairs xs).length +
      ((leftSpine (restrictTree (SplayTree.pop T) IM)).length +
        (rightSpine (restrictTree (SplayTree.pop T) IM)).length +
        (rightSpine (restrictTree (SplayTree.pop T) IL)).length +
        (leftSpine (restrictTree (SplayTree.pop T) IR)).length) ≤
      _ + ((leftSpine (restrictTree T IM)).length +
        (rightSpine (restrictTree T IM)).length +
        (rightSpine (restrictTree T IL)).length +
        (leftSpine (restrictTree T IR)).length) + 4
    omega
  have hk_le : ((leftSpine T).length - 1 : ℕ) ≤ 2 * (adjacentPairs xs).length + 1 := by
    have : popCascadePairs T = adjacentPairs xs := rfl
    rw [← this, hpairs_len]
    rcases hk_div with hk0 | hk1 <;> omega
  have hpairsL_out :
      (popCascadePairs T).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm)) =
        (adjacentPairs xs).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm)) := rfl
  have hpairsR_out :
      (popCascadePairs T).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2)) =
        (adjacentPairs xs).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2)) := rfl
  have hcost_real :
      popCost T + 2 * (spinePot Lm Rm (SplayTree.pop T) : ℝ) ≤
        2 * (((popCascadePairs T).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm))).length : ℝ) +
          2 * (spinePot Lm Rm T : ℝ) + 9 := by
    rw [hpairsL_out, hcost_eq]
    have hnat : ((leftSpine T).length - 1) + 2 * spinePot Lm Rm (SplayTree.pop T) ≤
        2 * ((adjacentPairs xs).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm))).length +
          2 * spinePot Lm Rm T + 9 := by
      omega
    exact_mod_cast hnat
  refine ⟨hcost_real, hU_ne, hRS_U_bound, ?_, ?_, ?_⟩
  · rw [hpairsR_out]; exact hW_ls_bound
  · intro p hp
    rw [hpairsR_out, ← hpairsR_eq] at hp
    have hres := hpairsR_props p hp
    rwa [hsplice_R] at hres
  · rw [hpairsR_out]; exact hW_eq'

private theorem eject_step_accounting
    (h_3_1 : Ty_lem_3_1) (h_3_2 : Ty_lem_3_2)
    {Lm Rm : ℝ} (hLmRm : Lm < Rm)
    (T : BinaryTree ℝ) (hT : T.IsBST) (hne : T ≠ .nil)
    (hmaxR : ∀ zMax : ℝ, T.maxKey? = some zMax → Rm ≤ zMax) :
    let T' := SplayTree.eject T
    let U := restrictTree T {x : ℝ | x ≤ Lm}
    let U' := restrictTree T' {x : ℝ | x ≤ Lm}
    let W := restrictTree T {x : ℝ | Rm ≤ x}
    let W' := restrictTree T' {x : ℝ | Rm ≤ x}
    let pairsR := (open Classical in
      (ejectCascadePairs T).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2)))
    let pairsL := (open Classical in
      (ejectCascadePairs T).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm)))
    ejectCost T + 2 * (spinePot Lm Rm T' : ℝ) ≤
      2 * (pairsR.length : ℝ) + 2 * (spinePot Lm Rm T : ℝ) + 9 ∧
    W ≠ .nil ∧
    (leftSpine W').length ≤ (leftSpine W).length + 1 ∧
    (rightSpine U').length + pairsL.length = (rightSpine U).length ∧
    (∀ p ∈ pairsL, p.1 ∈ rightSpine U ∧ p.2 ∈ rightSpine U ∧ p.2 < p.1) ∧
    U' = pairsL.foldl (fun acc p => rotateLeftEdge acc p.1 p.2) U := by
  classical
  let NT := negMirror T
  have hNT_bst : NT.IsBST := negMirror_isBST T hT
  have hNT_ne : NT ≠ .nil := mt (negMirror_eq_nil_iff T).mp hne
  have hLmRm' : -Rm < -Lm := neg_lt_neg hLmRm
  have hNT_min : ∀ yMin : ℝ, NT.minKey? = some yMin → yMin ≤ -Rm := by
    intro yMin hyMin
    rw [minKey?_negMirror] at hyMin
    cases hmax : T.maxKey? with
    | none => simp [hmax] at hyMin
    | some zMax =>
      simp only [hmax, Option.map_some, Option.some.injEq] at hyMin
      subst hyMin
      exact neg_le_neg (hmaxR zMax hmax)
  have hstep := pop_step_accounting h_3_1 h_3_2 hLmRm' NT hNT_bst hNT_ne hNT_min
  -- Relate SplayTree.pop NT and SplayTree.eject T via h_3_2
  obtain ⟨⟨_, _, _, hpop_cost_NT, hpop_eq_NT⟩, _⟩ := h_3_2 NT hNT_bst hNT_ne
  obtain ⟨_, ⟨_, _, _, hej_cost_T, hej_eq_T⟩⟩ := h_3_2 T hT hne
  have hpop_NT_eq : SplayTree.pop NT = negMirror (SplayTree.eject T) := by
    rw [hpop_eq_NT, hej_eq_T, popCascade_negMirror]
  have hcost_NT_eq : popCost NT = ejectCost T := by
    rw [hpop_cost_NT, hej_cost_T, leftSpine_negMirror, List.length_map]
  -- Relate interval projections of B and negMirror B
  have hproj_W : ∀ (B : BinaryTree ℝ), B.IsBST →
      restrictTree (negMirror B) {y : ℝ | y ≤ -Rm} =
        negMirror (restrictTree B {x : ℝ | Rm ≤ x}) := by
    intro B hB
    have hset : ({y : ℝ | y ≤ -Rm} : Set ℝ) = {y : ℝ | -y ∈ ({x : ℝ | Rm ≤ x} : Set ℝ)} := by
      ext y; simp [le_neg]
    rw [hset]
    exact restrictTree_negMirror B _ hB (ordConvex_Ici Rm)
  have hproj_M : ∀ (B : BinaryTree ℝ), B.IsBST →
      restrictTree (negMirror B) {y : ℝ | -Rm < y ∧ y < -Lm} =
        negMirror (restrictTree B {x : ℝ | Lm < x ∧ x < Rm}) := by
    intro B hB
    have hset : ({y : ℝ | -Rm < y ∧ y < -Lm} : Set ℝ) =
        {y : ℝ | -y ∈ ({x : ℝ | Lm < x ∧ x < Rm} : Set ℝ)} := by
      ext y; simp [lt_neg, neg_lt, and_comm]
    rw [hset]
    exact restrictTree_negMirror B _ hB (ordConvex_Ioo Lm Rm)
  have hproj_U : ∀ (B : BinaryTree ℝ), B.IsBST →
      restrictTree (negMirror B) {y : ℝ | -Lm ≤ y} =
        negMirror (restrictTree B {x : ℝ | x ≤ Lm}) := by
    intro B hB
    have hset : ({y : ℝ | -Lm ≤ y} : Set ℝ) = {y : ℝ | -y ∈ ({x : ℝ | x ≤ Lm} : Set ℝ)} := by
      ext y; simp [neg_le]
    rw [hset]
    exact restrictTree_negMirror B _ hB (ordConvex_Iic Lm)
  have hpot_eq : ∀ (B : BinaryTree ℝ), B.IsBST →
      spinePot (-Rm) (-Lm) (negMirror B) = spinePot Lm Rm B := by
    intro B hB
    unfold spinePot
    dsimp only
    rw [hproj_W B hB, hproj_M B hB, hproj_U B hB,
      leftSpine_negMirror, rightSpine_negMirror, rightSpine_negMirror, leftSpine_negMirror]
    simp only [rightSpineBottomUp, List.length_map, List.length_reverse]
    omega
  obtain ⟨_, _, _, _, _, _, _, hejT_bst, _, _⟩ := eject_spec_poly T hT hne
  have hpot_T : spinePot (-Rm) (-Lm) NT = spinePot Lm Rm T := hpot_eq T hT
  have hpot_T' : spinePot (-Rm) (-Lm) (SplayTree.pop NT) = spinePot Lm Rm (SplayTree.eject T) := by
    rw [hpop_NT_eq]
    exact hpot_eq (SplayTree.eject T) hejT_bst
  have hpairs_L_NT :
      (popCascadePairs NT).filter (fun q => decide (q.1 ≤ -Rm ∧ q.2 ≤ -Rm)) =
        ((ejectCascadePairs T).filter (fun p => decide (Rm ≤ p.1 ∧ Rm ≤ p.2))).map
          (fun p => (-p.1, -p.2)) := by
    rw [popCascadePairs_negMirror, List.filter_map]
    congr 1
    exact List.filter_congr (fun p _ => by simp)
  have hpairs_R_NT :
      (popCascadePairs NT).filter (fun q => decide (-Lm ≤ q.1 ∧ -Lm ≤ q.2)) =
        ((ejectCascadePairs T).filter (fun p => decide (p.1 ≤ Lm ∧ p.2 ≤ Lm))).map
          (fun p => (-p.1, -p.2)) := by
    rw [popCascadePairs_negMirror, List.filter_map]
    congr 1
    exact List.filter_congr (fun p _ => by simp)
  rcases hstep with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcost_NT_eq, hpot_T', hpot_T, hpairs_L_NT, List.length_map] at h1
    exact h1
  · rw [hproj_W T hT] at h2
    exact mt (negMirror_eq_nil_iff _).mpr h2
  · rw [hpop_NT_eq, hproj_W (SplayTree.eject T) hejT_bst, hproj_W T hT,
      rightSpine_negMirror, rightSpine_negMirror] at h3
    simpa only [List.length_map, List.length_reverse] using h3
  · rw [hpop_NT_eq, hproj_U (SplayTree.eject T) hejT_bst, hproj_U T hT,
      leftSpine_negMirror, leftSpine_negMirror, hpairs_R_NT] at h4
    simpa only [rightSpineBottomUp, List.length_map, List.length_reverse] using h4
  · intro p hp
    have hq_in : (-p.1, -p.2) ∈
        (popCascadePairs NT).filter (fun q => decide (-Lm ≤ q.1 ∧ -Lm ≤ q.2)) := by
      rw [hpairs_R_NT]
      exact List.mem_map_of_mem hp
    rcases h5 (-p.1, -p.2) hq_in with ⟨hq1, hq2, hqlt⟩
    rw [hproj_U T hT, leftSpine_negMirror] at hq1 hq2
    simp only [rightSpineBottomUp, List.mem_map, List.mem_reverse, neg_inj] at hq1 hq2
    rcases hq1 with ⟨a1, ha1, ha1_eq⟩; subst ha1_eq
    rcases hq2 with ⟨a2, ha2, ha2_eq⟩; subst ha2_eq
    exact ⟨ha1, ha2, neg_lt_neg_iff.mp hqlt⟩
  · rw [hpop_NT_eq, hproj_U (SplayTree.eject T) hejT_bst, hproj_U T hT,
      hpairs_R_NT, List.foldl_map] at h6
    have hfold_neg : ∀ (ps : List (ℝ × ℝ)) (acc : BinaryTree ℝ),
        ps.foldl (fun a p => rotateRightEdge a (-p.1) (-p.2)) (negMirror acc) =
          negMirror (ps.foldl (fun a p => rotateLeftEdge a p.1 p.2) acc) := by
      intro ps
      induction ps with
      | nil => intro acc; rfl
      | cons p rest ih =>
        intro acc
        simp only [List.foldl_cons, rotateRightEdge_negMirror]
        exact ih (rotateLeftEdge acc p.1 p.2)
    rw [hfold_neg] at h6
    have h7 := congrArg negMirror h6
    simpa only [negMirror_involutive] using h7

/-! ### Sequence-Level Spine Accounting Assembly (`lem_3_4_spine_accounting`) -/

private theorem sum_fin_telescope_nat {m : ℕ} (f : Fin (m + 1) → ℕ) :
    f 0 + ∑ i : Fin m, f i.succ = f (Fin.last m) + ∑ i : Fin m, f i.castSucc := by
  induction m with
  | zero => simp [Fin.last]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h0 : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := rfl
    have hlast : (Fin.last m).succ = Fin.last (m + 1) := rfl
    have hcomm : ∀ j : Fin m, j.castSucc.succ = j.succ.castSucc := fun _ => rfl
    have hih := ih (fun j => f j.castSucc)
    simp only [h0, ← hlast, hcomm] at *
    omega

private theorem sum_fin_telescope_real {m : ℕ} (f : Fin (m + 1) → ℝ) :
    f 0 + ∑ i : Fin m, (f i.succ - f i.castSucc) = f (Fin.last m) := by
  induction m with
  | zero => simp [Fin.last]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have h0 : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := rfl
    have hlast : (Fin.last m).succ = Fin.last (m + 1) := rfl
    have hcomm : ∀ j : Fin m, j.castSucc.succ = j.succ.castSucc := fun _ => rfl
    have hih := ih (fun j => f j.castSucc)
    simp only [hcomm]
    rw [h0, ← add_assoc, hih, ← hlast]
    ring

private theorem fin_mono_from {m : ℕ} (f : Fin (m + 1) → ℕ) (k : Fin (m + 1))
    (hstep : ∀ j : Fin m, k ≤ j.castSucc → f j.castSucc ≤ f j.succ) :
    ∀ t : Fin (m + 1), k ≤ t → f k ≤ f t := by
  intro t hkt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, t.val = k.val + d := Nat.exists_eq_add_of_le (Fin.le_def.mp hkt)
  induction d generalizing t with
  | zero =>
    have ht : t = k := Fin.ext (by omega)
    subst ht
    exact le_rfl
  | succ d ih =>
    let j : Fin m := ⟨k.val + d, by omega⟩
    have hj_succ : j.succ = t := Fin.ext (by simp [j, hd, Nat.add_assoc])
    have hkj : k ≤ j.castSucc := Fin.le_def.mpr (by simp [j])
    calc f k ≤ f j.castSucc := ih j.castSucc hkj (by simp [j])
      _ ≤ f j.succ := hstep j hkj
      _ = f t := by rw [hj_succ]

private theorem asn_isPop_eq {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) :
    (ops i).isPop = (asn.opsR i).isPop := by
  have h := asn.hKind i
  revert h
  cases ops i <;> cases asn.opsR i <;> simp [DequeOp.sameKind, DequeOp.isPop]

private theorem asn_isEject_eq {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) :
    (ops i).isEject = (asn.opsR i).isEject := by
  have h := asn.hKind i
  revert h
  cases ops i <;> cases asn.opsR i <;> simp [DequeOp.sameKind, DequeOp.isEject]

private theorem asn_pop_min_le_Lm {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m)
    (hpop : (asn.opsR i).isPop) (xMin : ℝ)
    (hmin : (asn.treeAt i.castSucc).minKey? = some xMin) :
    xMin ≤ asn.Lm := by
  classical
  have hmem_list : xMin ∈ popDeletedKeys asn.T0 asn.opsR := by
    unfold popDeletedKeys
    rw [List.mem_filterMap]
    refine ⟨i, List.mem_finRange i, ?_⟩
    simpa [ThreeWayKeyAssignment.treeAt, hpop] using hmin
  have hmem_fin : xMin ∈ (popDeletedKeys asn.T0 asn.opsR).toFinset :=
    List.mem_toFinset.mpr hmem_list
  rw [asn.hPopOrder.2.2] at hmem_fin
  exact (Finset.mem_filter.mp hmem_fin).2

private theorem asn_eject_max_ge_Rm {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m)
    (hej : (asn.opsR i).isEject) (zMax : ℝ)
    (hmax : (asn.treeAt i.castSucc).maxKey? = some zMax) :
    asn.Rm ≤ zMax := by
  classical
  have hmem_list : zMax ∈ ejectDeletedKeys asn.T0 asn.opsR := by
    unfold ejectDeletedKeys
    rw [List.mem_filterMap]
    refine ⟨i, List.mem_finRange i, ?_⟩
    simpa [ThreeWayKeyAssignment.treeAt, hej] using hmax
  have hmem_fin : zMax ∈ (ejectDeletedKeys asn.T0 asn.opsR).toFinset :=
    List.mem_toFinset.mpr hmem_list
  rw [asn.hEjectOrder.2.2] at hmem_fin
  exact (Finset.mem_filter.mp hmem_fin).2

private theorem mem_ever_of_popCascadePairs {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) {p : ℝ × ℝ}
    (hp : p ∈ popCascadePairs (asn.treeAt t)) :
    p.1 ∈ asn.everPresentKeys ∧ p.2 ∈ asn.everPresentKeys := by
  classical
  rcases mem_of_mem_adjacentPairs hp with ⟨h1, h2⟩
  have hm1 : p.1 ∈ asn.treeAt t := mem_leftSpine_mem (List.mem_of_mem_tail h1)
  have hm2 : p.2 ∈ asn.treeAt t := mem_leftSpine_mem (List.mem_of_mem_tail h2)
  exact ⟨asn.hActiveSub t ((mem_keyFinset_iff _ _).mpr hm1),
    asn.hActiveSub t ((mem_keyFinset_iff _ _).mpr hm2)⟩

private theorem mem_ever_of_ejectCascadePairs {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) {p : ℝ × ℝ}
    (hp : p ∈ ejectCascadePairs (asn.treeAt t)) :
    p.1 ∈ asn.everPresentKeys ∧ p.2 ∈ asn.everPresentKeys := by
  classical
  rcases mem_of_mem_adjacentPairs hp with ⟨h1, h2⟩
  have hr1 : p.1 ∈ rightSpine (asn.treeAt t) :=
    List.mem_reverse.mp (List.mem_of_mem_tail h1)
  have hr2 : p.2 ∈ rightSpine (asn.treeAt t) :=
    List.mem_reverse.mp (List.mem_of_mem_tail h2)
  have hm1 : p.1 ∈ asn.treeAt t := mem_rightSpine_mem hr1
  have hm2 : p.2 ∈ asn.treeAt t := mem_rightSpine_mem hr2
  exact ⟨asn.hActiveSub t ((mem_keyFinset_iff _ _).mpr hm1),
    asn.hActiveSub t ((mem_keyFinset_iff _ _).mpr hm2)⟩

private theorem asn_popPairs_VL_eq {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) :
    (open Classical in
      (popCascadePairs (asn.treeAt t)).filter (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)) =
    (open Classical in
      (popCascadePairs (asn.treeAt t)).filter (fun p => decide (p.1 ≤ asn.Lm ∧ p.2 ≤ asn.Lm))) := by
  refine List.filter_congr (fun p hp => ?_)
  rcases mem_ever_of_popCascadePairs asn t hp with ⟨he1, he2⟩
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, ThreeWayKeyAssignment.VL, Finset.mem_filter]
  exact ⟨fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨he1, h1⟩, ⟨he2, h2⟩⟩⟩

private theorem asn_popPairs_VR_eq {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) :
    (open Classical in
      (popCascadePairs (asn.treeAt t)).filter (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)) =
    (open Classical in
      (popCascadePairs (asn.treeAt t)).filter (fun p => decide (asn.Rm ≤ p.1 ∧ asn.Rm ≤ p.2))) := by
  refine List.filter_congr (fun p hp => ?_)
  rcases mem_ever_of_popCascadePairs asn t hp with ⟨he1, he2⟩
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, ThreeWayKeyAssignment.VR, Finset.mem_filter]
  exact ⟨fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨he1, h1⟩, ⟨he2, h2⟩⟩⟩

private theorem asn_ejPairs_VR_eq {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) :
    (open Classical in
      (ejectCascadePairs (asn.treeAt t)).filter (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)) =
    (open Classical in
      (ejectCascadePairs (asn.treeAt t)).filter (fun p => decide (asn.Rm ≤ p.1 ∧ asn.Rm ≤ p.2))) := by
  refine List.filter_congr (fun p hp => ?_)
  rcases mem_ever_of_ejectCascadePairs asn t hp with ⟨he1, he2⟩
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, ThreeWayKeyAssignment.VR, Finset.mem_filter]
  exact ⟨fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨he1, h1⟩, ⟨he2, h2⟩⟩⟩

private theorem asn_ejPairs_VL_eq {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) :
    (open Classical in
      (ejectCascadePairs (asn.treeAt t)).filter (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)) =
    (open Classical in
      (ejectCascadePairs (asn.treeAt t)).filter (fun p => decide (p.1 ≤ asn.Lm ∧ p.2 ≤ asn.Lm))) := by
  refine List.filter_congr (fun p hp => ?_)
  rcases mem_ever_of_ejectCascadePairs asn t hp with ⟨he1, he2⟩
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, ThreeWayKeyAssignment.VL, Finset.mem_filter]
  exact ⟨fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨he1, h1⟩, ⟨he2, h2⟩⟩⟩

private theorem asn_init_pot_le (h_3_1 : Ty_lem_3_1)
    {α : Type} [LinearOrder α] {n m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (hn : init.tree.num_nodes = n)
    (asn : ThreeWayKeyAssignment init ops) :
    spinePot asn.Lm asn.Rm asn.T0 ≤ 2 * n := by
  classical
  have hT0_bst : asn.T0.IsBST := asn.hBST 0
  have hT0_nodes : asn.T0.num_nodes = n := by
    have hsh := congrArg BinaryTree.num_nodes (asn.hShape 0)
    simpa only [dequeSeq_zero, map_num_nodes, hn] using hsh
  let IL : Set ℝ := {x : ℝ | x ≤ asn.Lm}
  let IM : Set ℝ := {x : ℝ | asn.Lm < x ∧ x < asn.Rm}
  let IR : Set ℝ := {x : ℝ | asn.Rm ≤ x}
  obtain ⟨⟨hU_bst, hU_mem⟩, _, _⟩ :=
    h_3_1 asn.T0 IL hT0_bst (isLCAClosed_of_ordConvex (ordConvex_Iic asn.Lm) asn.T0)
  obtain ⟨⟨hM_bst, hM_mem⟩, _, _⟩ :=
    h_3_1 asn.T0 IM hT0_bst (isLCAClosed_of_ordConvex (ordConvex_Ioo asn.Lm asn.Rm) asn.T0)
  obtain ⟨⟨hW_bst, hW_mem⟩, _, _⟩ :=
    h_3_1 asn.T0 IR hT0_bst (isLCAClosed_of_ordConvex (ordConvex_Ici asn.Rm) asn.T0)
  have hU_kf : keyFinset (restrictTree asn.T0 IL) = (keyFinset asn.T0).filter (· ≤ asn.Lm) := by
    ext v; simp [mem_keyFinset_iff, hU_mem, IL]
  have hM_kf : keyFinset (restrictTree asn.T0 IM) =
      (keyFinset asn.T0).filter (fun x => asn.Lm < x ∧ x < asn.Rm) := by
    ext v; simp [mem_keyFinset_iff, hM_mem, IM]
  have hW_kf : keyFinset (restrictTree asn.T0 IR) = (keyFinset asn.T0).filter (asn.Rm ≤ ·) := by
    ext v; simp [mem_keyFinset_iff, hW_mem, IR]
  have hU_n : (restrictTree asn.T0 IL).num_nodes =
      ((keyFinset asn.T0).filter (· ≤ asn.Lm)).card := by
    rw [← card_keyFinset_of_isBST _ hU_bst, hU_kf]
  have hM_n : (restrictTree asn.T0 IM).num_nodes =
      ((keyFinset asn.T0).filter (fun x => asn.Lm < x ∧ x < asn.Rm)).card := by
    rw [← card_keyFinset_of_isBST _ hM_bst, hM_kf]
  have hW_n : (restrictTree asn.T0 IR).num_nodes =
      ((keyFinset asn.T0).filter (asn.Rm ≤ ·)).card := by
    rw [← card_keyFinset_of_isBST _ hW_bst, hW_kf]
  have hdisj_LM : Disjoint ((keyFinset asn.T0).filter (· ≤ asn.Lm))
      ((keyFinset asn.T0).filter (fun x => asn.Lm < x ∧ x < asn.Rm)) := by
    rw [Finset.disjoint_left]
    intro x hxL hxM
    exact not_lt_of_ge (Finset.mem_filter.mp hxL).2 (Finset.mem_filter.mp hxM).2.1
  have hdisj_LMR : Disjoint
      (((keyFinset asn.T0).filter (· ≤ asn.Lm)) ∪
        ((keyFinset asn.T0).filter (fun x => asn.Lm < x ∧ x < asn.Rm)))
      ((keyFinset asn.T0).filter (asn.Rm ≤ ·)) := by
    rw [Finset.disjoint_left]
    intro x hxLM hxR
    have hxR' : asn.Rm ≤ x := (Finset.mem_filter.mp hxR).2
    rcases Finset.mem_union.mp hxLM with hxL | hxM
    · exact not_lt_of_ge (le_trans hxR' (Finset.mem_filter.mp hxL).2) asn.hLmRm
    · exact not_lt_of_ge hxR' (Finset.mem_filter.mp hxM).2.2
  have hsub : (((keyFinset asn.T0).filter (· ≤ asn.Lm)) ∪
      ((keyFinset asn.T0).filter (fun x => asn.Lm < x ∧ x < asn.Rm))) ∪
      ((keyFinset asn.T0).filter (asn.Rm ≤ ·)) ⊆ keyFinset asn.T0 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxLM | hxR
    · rcases Finset.mem_union.mp hxLM with hxL | hxM
      · exact (Finset.mem_filter.mp hxL).1
      · exact (Finset.mem_filter.mp hxM).1
    · exact (Finset.mem_filter.mp hxR).1
  have hsum_n : (restrictTree asn.T0 IL).num_nodes +
      (restrictTree asn.T0 IM).num_nodes +
      (restrictTree asn.T0 IR).num_nodes ≤ n := by
    rw [hU_n, hM_n, hW_n, ← Finset.card_union_of_disjoint hdisj_LM,
      ← Finset.card_union_of_disjoint hdisj_LMR, ← hT0_nodes,
      ← card_keyFinset_of_isBST _ hT0_bst]
    exact Finset.card_le_card hsub
  have h1 := leftSpine_length_le_num_nodes (restrictTree asn.T0 IM)
  have h2 := rightSpine_length_le_num_nodes (restrictTree asn.T0 IM)
  have h3 := rightSpine_length_le_num_nodes (restrictTree asn.T0 IL)
  have h4 := leftSpine_length_le_num_nodes (restrictTree asn.T0 IR)
  unfold spinePot
  dsimp only
  change (leftSpine (restrictTree asn.T0 IM)).length +
    (rightSpine (restrictTree asn.T0 IM)).length +
    (rightSpine (restrictTree asn.T0 IL)).length +
    (leftSpine (restrictTree asn.T0 IR)).length ≤ 2 * n
  omega

private theorem push_pot_and_spines {Lm Rm : ℝ} (hLmRm : Lm < Rm)
    (T : BinaryTree ℝ) (q : ℝ) :
    spinePot Lm Rm (SplayTree.push T q) ≤ spinePot Lm Rm T + 2 ∧
    (rightSpine (restrictTree (SplayTree.push T q) {x : ℝ | x ≤ Lm})).length ≤
      (rightSpine (restrictTree T {x : ℝ | x ≤ Lm})).length +
        (open Classical in if q ≤ Lm then 1 else 0) ∧
    (leftSpine (restrictTree (SplayTree.push T q) {x : ℝ | Rm ≤ x})).length ≤
      (leftSpine (restrictTree T {x : ℝ | Rm ≤ x})).length +
        (open Classical in if Rm ≤ q then 1 else 0) := by
  classical
  unfold spinePot
  dsimp only
  rw [restrictTree_push T q {x : ℝ | x ≤ Lm},
    restrictTree_push T q {x : ℝ | Lm < x ∧ x < Rm},
    restrictTree_push T q {x : ℝ | Rm ≤ x}]
  by_cases hqL : q ≤ Lm
  · have hnotM : q ∉ ({x : ℝ | Lm < x ∧ x < Rm} : Set ℝ) := fun h => not_lt_of_ge hqL h.1
    have hnotR : q ∉ ({x : ℝ | Rm ≤ x} : Set ℝ) :=
      fun h => not_lt_of_ge (le_trans h hqL) hLmRm
    have hnotR' : ¬(Rm ≤ q) := hnotR
    have hqL_mem : q ∈ ({x : ℝ | x ≤ Lm} : Set ℝ) := hqL
    simp only [hqL_mem, hqL, hnotM, hnotR, hnotR', ↓reduceIte, rightSpine, List.length_cons]
    omega
  · by_cases hqR : Rm ≤ q
    · have hnotL : q ∉ ({x : ℝ | x ≤ Lm} : Set ℝ) := hqL
      have hnotM : q ∉ ({x : ℝ | Lm < x ∧ x < Rm} : Set ℝ) := fun h => not_lt_of_ge hqR h.2
      have hqR_mem : q ∈ ({x : ℝ | Rm ≤ x} : Set ℝ) := hqR
      simp only [hnotL, hqL, hnotM, hqR_mem, hqR, ↓reduceIte, leftSpine,
        List.nil_append, List.length_singleton]
      omega
    · have hnotL : q ∉ ({x : ℝ | x ≤ Lm} : Set ℝ) := hqL
      have hnotR : q ∉ ({x : ℝ | Rm ≤ x} : Set ℝ) := hqR
      have hqM : q ∈ ({x : ℝ | Lm < x ∧ x < Rm} : Set ℝ) := ⟨lt_of_not_ge hqL, lt_of_not_ge hqR⟩
      simp only [hnotL, hqL, hqM, hnotR, hqR, ↓reduceIte, leftSpine, rightSpine,
        List.nil_append, List.length_cons, List.length_nil]
      omega

private theorem inject_pot_and_spines {Lm Rm : ℝ} (hLmRm : Lm < Rm)
    (T : BinaryTree ℝ) (q : ℝ) :
    spinePot Lm Rm (SplayTree.inject T q) ≤ spinePot Lm Rm T + 2 ∧
    (rightSpine (restrictTree (SplayTree.inject T q) {x : ℝ | x ≤ Lm})).length ≤
      (rightSpine (restrictTree T {x : ℝ | x ≤ Lm})).length +
        (open Classical in if q ≤ Lm then 1 else 0) ∧
    (leftSpine (restrictTree (SplayTree.inject T q) {x : ℝ | Rm ≤ x})).length ≤
      (leftSpine (restrictTree T {x : ℝ | Rm ≤ x})).length +
        (open Classical in if Rm ≤ q then 1 else 0) := by
  classical
  unfold spinePot
  dsimp only
  rw [restrictTree_inject T q {x : ℝ | x ≤ Lm},
    restrictTree_inject T q {x : ℝ | Lm < x ∧ x < Rm},
    restrictTree_inject T q {x : ℝ | Rm ≤ x}]
  by_cases hqL : q ≤ Lm
  · have hnotM : q ∉ ({x : ℝ | Lm < x ∧ x < Rm} : Set ℝ) := fun h => not_lt_of_ge hqL h.1
    have hnotR : q ∉ ({x : ℝ | Rm ≤ x} : Set ℝ) :=
      fun h => not_lt_of_ge (le_trans h hqL) hLmRm
    have hnotR' : ¬(Rm ≤ q) := hnotR
    have hqL_mem : q ∈ ({x : ℝ | x ≤ Lm} : Set ℝ) := hqL
    simp only [hqL_mem, hqL, hnotM, hnotR, hnotR', ↓reduceIte, rightSpine, List.length_singleton]
    omega
  · by_cases hqR : Rm ≤ q
    · have hnotL : q ∉ ({x : ℝ | x ≤ Lm} : Set ℝ) := hqL
      have hnotM : q ∉ ({x : ℝ | Lm < x ∧ x < Rm} : Set ℝ) := fun h => not_lt_of_ge hqR h.2
      have hqR_mem : q ∈ ({x : ℝ | Rm ≤ x} : Set ℝ) := hqR
      simp only [hnotL, hqL, hnotM, hqR_mem, hqR, ↓reduceIte, leftSpine,
        List.length_append, List.length_singleton]
      omega
    · have hnotL : q ∉ ({x : ℝ | x ≤ Lm} : Set ℝ) := hqL
      have hnotR : q ∉ ({x : ℝ | Rm ≤ x} : Set ℝ) := hqR
      have hqM : q ∈ ({x : ℝ | Lm < x ∧ x < Rm} : Set ℝ) := ⟨lt_of_not_ge hqL, lt_of_not_ge hqR⟩
      simp only [hnotL, hqL, hqM, hnotR, hqR, ↓reduceIte, leftSpine, rightSpine,
        List.length_append, List.length_singleton]
      omega

private noncomputable def countLE (L : ℝ) (T : BinaryTree ℝ) : ℕ :=
  open Classical in (T.toKeyList.filter (fun x => decide (x ≤ L))).length

private noncomputable def countGE (R : ℝ) (T : BinaryTree ℝ) : ℕ :=
  open Classical in (T.toKeyList.filter (fun x => decide (R ≤ x))).length

private noncomputable def opInsLE (L : ℝ) : DequeOp ℝ → ℕ
  | .push q => open Classical in if q ≤ L then 1 else 0
  | .inject q => open Classical in if q ≤ L then 1 else 0
  | _ => 0

private noncomputable def opInsGE (R : ℝ) : DequeOp ℝ → ℕ
  | .push q => open Classical in if R ≤ q then 1 else 0
  | .inject q => open Classical in if R ≤ q then 1 else 0
  | _ => 0

private theorem restrictTree_Iic_nodes_le_countLE (h_3_1 : Ty_lem_3_1)
    (T : BinaryTree ℝ) (L : ℝ) (hT : T.IsBST) :
    (restrictTree T {x : ℝ | x ≤ L}).num_nodes ≤ countLE L T := by
  classical
  obtain ⟨⟨hB_bst, hB_mem⟩, _, _⟩ :=
    h_3_1 T {x : ℝ | x ≤ L} hT (isLCAClosed_of_ordConvex (ordConvex_Iic L) T)
  rw [← card_keyFinset_of_isBST _ hB_bst]
  have hsub : keyFinset (restrictTree T {x : ℝ | x ≤ L}) ⊆
      (T.toKeyList.filter (fun x => decide (x ≤ L))).toFinset := by
    intro v hv
    rcases (hB_mem v).mp ((mem_keyFinset_iff _ _).mp hv) with ⟨hvT, hvL⟩
    exact List.mem_toFinset.mpr
      (List.mem_filter.mpr ⟨mem_iff_mem_toKeyList.mp hvT, decide_eq_true hvL⟩)
  exact le_trans (Finset.card_le_card hsub) (List.toFinset_card_le _)

private theorem restrictTree_Ici_nodes_le_countGE (h_3_1 : Ty_lem_3_1)
    (T : BinaryTree ℝ) (R : ℝ) (hT : T.IsBST) :
    (restrictTree T {x : ℝ | R ≤ x}).num_nodes ≤ countGE R T := by
  classical
  obtain ⟨⟨hB_bst, hB_mem⟩, _, _⟩ :=
    h_3_1 T {x : ℝ | R ≤ x} hT (isLCAClosed_of_ordConvex (ordConvex_Ici R) T)
  rw [← card_keyFinset_of_isBST _ hB_bst]
  have hsub : keyFinset (restrictTree T {x : ℝ | R ≤ x}) ⊆
      (T.toKeyList.filter (fun x => decide (R ≤ x))).toFinset := by
    intro v hv
    rcases (hB_mem v).mp ((mem_keyFinset_iff _ _).mp hv) with ⟨hvT, hvR⟩
    exact List.mem_toFinset.mpr
      (List.mem_filter.mpr ⟨mem_iff_mem_toKeyList.mp hvT, decide_eq_true hvR⟩)
  exact le_trans (Finset.card_le_card hsub) (List.toFinset_card_le _)

private theorem restrictTree_Iic_eq_nil_of_countLE_zero
    (T : BinaryTree ℝ) (L : ℝ) (h : countLE L T = 0) :
    restrictTree T {x : ℝ | x ≤ L} = .nil := by
  classical
  unfold countLE at h
  have hnil : T.toKeyList.filter (fun x => decide (x ≤ L)) = [] :=
    List.length_eq_zero_iff.mp h
  refine restrictTree_eq_nil_of_disjoint T {x : ℝ | x ≤ L} (fun x hx hxL => ?_)
  have hx_in : x ∈ T.toKeyList.filter (fun y => decide (y ≤ L)) :=
    List.mem_filter.mpr ⟨mem_iff_mem_toKeyList.mp hx, decide_eq_true hxL⟩
  rw [hnil] at hx_in
  simp at hx_in

private theorem restrictTree_Ici_eq_nil_of_countGE_zero
    (T : BinaryTree ℝ) (R : ℝ) (h : countGE R T = 0) :
    restrictTree T {x : ℝ | R ≤ x} = .nil := by
  classical
  unfold countGE at h
  have hnil : T.toKeyList.filter (fun x => decide (R ≤ x)) = [] :=
    List.length_eq_zero_iff.mp h
  refine restrictTree_eq_nil_of_disjoint T {x : ℝ | R ≤ x} (fun x hx hxR => ?_)
  have hx_in : x ∈ T.toKeyList.filter (fun y => decide (R ≤ y)) :=
    List.mem_filter.mpr ⟨mem_iff_mem_toKeyList.mp hx, decide_eq_true hxR⟩
  rw [hnil] at hx_in
  simp at hx_in

private theorem asn_countLE_step {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) :
    countLE asn.Lm (asn.treeAt i.succ) + (if (asn.opsR i).isPop then 1 else 0) =
      countLE asn.Lm (asn.treeAt i.castSucc) + opInsLE asn.Lm (asn.opsR i) := by
  classical
  have hstep_eq : asn.treeAt i.succ = (asn.opsR i).step (asn.treeAt i.castSucc) :=
    dequeSeq_step asn.T0 asn.opsR i
  have hbst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
  have hval := asn.hValidR i
  change (asn.opsR i).Valid (asn.treeAt i.castSucc) at hval
  cases hop : asn.opsR i with
  | push q =>
    rw [hop] at hstep_eq
    simp only [DequeOp.step, SplayTree.push, DequeOp.isPop, Bool.false_eq_true, ↓reduceIte,
      opInsLE, countLE, hstep_eq, toKeyList, List.nil_append]
    by_cases hq : q ≤ asn.Lm <;> simp [hq]
  | inject q =>
    rw [hop] at hstep_eq
    simp only [DequeOp.step, SplayTree.inject, DequeOp.isPop, Bool.false_eq_true, ↓reduceIte,
      opInsLE, countLE, hstep_eq, toKeyList, List.append_nil, List.filter_append, List.filter_cons,
      List.filter_nil, List.length_append]
    by_cases hq : q ≤ asn.Lm <;> simp [hq]
  | pop =>
    rw [hop] at hstep_eq hval
    have hne : asn.treeAt i.castSucc ≠ .nil := hval
    obtain ⟨xMin, hxMin, _, _, _, _, htkl, _, _, _⟩ := pop_spec_poly (asn.treeAt i.castSucc) hbst hne
    have hxL : xMin ≤ asn.Lm :=
      asn_pop_min_le_Lm asn i (by simp [hop, DequeOp.isPop]) xMin hxMin
    simp only [DequeOp.step] at hstep_eq
    simp only [DequeOp.isPop, ↓reduceIte, opInsLE, countLE]
    rw [htkl, ← hstep_eq]
    simp only [List.filter_cons, hxL, decide_true, ↓reduceIte, List.length_cons]
  | eject =>
    rw [hop] at hstep_eq hval
    have hne : asn.treeAt i.castSucc ≠ .nil := hval
    obtain ⟨zMax, hzMax, _, _, _, _, htkl, _, _, _⟩ :=
      eject_spec_poly (asn.treeAt i.castSucc) hbst hne
    have hzR : asn.Rm ≤ zMax :=
      asn_eject_max_ge_Rm asn i (by simp [hop, DequeOp.isEject]) zMax hzMax
    have hnotL : ¬(zMax ≤ asn.Lm) :=
      fun h => not_lt_of_ge (le_trans hzR h) asn.hLmRm
    simp only [DequeOp.step] at hstep_eq
    simp only [DequeOp.isPop, Bool.false_eq_true, ↓reduceIte, opInsLE, countLE]
    rw [htkl, ← hstep_eq]
    simp [List.filter_append, hnotL]

private theorem asn_countGE_step {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) :
    countGE asn.Rm (asn.treeAt i.succ) + (if (asn.opsR i).isEject then 1 else 0) =
      countGE asn.Rm (asn.treeAt i.castSucc) + opInsGE asn.Rm (asn.opsR i) := by
  classical
  have hstep_eq : asn.treeAt i.succ = (asn.opsR i).step (asn.treeAt i.castSucc) :=
    dequeSeq_step asn.T0 asn.opsR i
  have hbst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
  have hval := asn.hValidR i
  change (asn.opsR i).Valid (asn.treeAt i.castSucc) at hval
  cases hop : asn.opsR i with
  | push q =>
    rw [hop] at hstep_eq
    simp only [DequeOp.step, SplayTree.push, DequeOp.isEject, Bool.false_eq_true, ↓reduceIte,
      opInsGE, countGE, hstep_eq, toKeyList, List.nil_append]
    by_cases hq : asn.Rm ≤ q <;> simp [hq]
  | inject q =>
    rw [hop] at hstep_eq
    simp only [DequeOp.step, SplayTree.inject, DequeOp.isEject, Bool.false_eq_true, ↓reduceIte,
      opInsGE, countGE, hstep_eq, toKeyList, List.append_nil, List.filter_append, List.filter_cons,
      List.filter_nil, List.length_append]
    by_cases hq : asn.Rm ≤ q <;> simp [hq]
  | pop =>
    rw [hop] at hstep_eq hval
    have hne : asn.treeAt i.castSucc ≠ .nil := hval
    obtain ⟨xMin, hxMin, _, _, _, _, htkl, _, _, _⟩ := pop_spec_poly (asn.treeAt i.castSucc) hbst hne
    have hxL : xMin ≤ asn.Lm :=
      asn_pop_min_le_Lm asn i (by simp [hop, DequeOp.isPop]) xMin hxMin
    have hnotR : ¬(asn.Rm ≤ xMin) :=
      fun h => not_lt_of_ge (le_trans h hxL) asn.hLmRm
    simp only [DequeOp.step] at hstep_eq
    simp only [DequeOp.isEject, Bool.false_eq_true, ↓reduceIte, opInsGE, countGE]
    rw [htkl, ← hstep_eq]
    simp [hnotR]
  | eject =>
    rw [hop] at hstep_eq hval
    have hne : asn.treeAt i.castSucc ≠ .nil := hval
    obtain ⟨zMax, hzMax, _, _, _, _, htkl, _, _, _⟩ :=
      eject_spec_poly (asn.treeAt i.castSucc) hbst hne
    have hzR : asn.Rm ≤ zMax :=
      asn_eject_max_ge_Rm asn i (by simp [hop, DequeOp.isEject]) zMax hzMax
    simp only [DequeOp.step] at hstep_eq
    simp only [DequeOp.isEject, ↓reduceIte, opInsGE, countGE]
    rw [htkl, ← hstep_eq]
    simp only [List.filter_append, List.filter_cons, List.filter_nil,
      hzR, decide_true, ↓reduceIte, List.length_append, List.length_singleton]

private theorem asn_countLE_last_zero {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) :
    countLE asn.Lm (asn.treeAt (Fin.last m)) = 0 := by
  classical
  unfold countLE
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  simp only [decide_eq_true_eq]
  intro hxL
  have hmem : x ∈ keyFinset (dequeSeq asn.T0 asn.opsR (Fin.last m)) :=
    (mem_keyFinset_iff _ _).mpr (mem_iff_mem_toKeyList.mpr hx)
  rw [asn.hSurviving] at hmem
  exact not_lt_of_ge hxL (Finset.mem_filter.mp hmem).2.1

private theorem asn_countGE_last_zero {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) :
    countGE asn.Rm (asn.treeAt (Fin.last m)) = 0 := by
  classical
  unfold countGE
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  simp only [decide_eq_true_eq]
  intro hxR
  have hmem : x ∈ keyFinset (dequeSeq asn.T0 asn.opsR (Fin.last m)) :=
    (mem_keyFinset_iff _ _).mpr (mem_iff_mem_toKeyList.mpr hx)
  rw [asn.hSurviving] at hmem
  exact not_lt_of_ge hxR (Finset.mem_filter.mp hmem).2.2

private theorem asn_total_countLE {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) :
    countLE asn.Lm (asn.treeAt 0) + ∑ i : Fin m, opInsLE asn.Lm (asn.opsR i) =
      popCount ops := by
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ)
    (fun i _ => asn_countLE_step asn i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have htel := sum_fin_telescope_nat (fun t => countLE asn.Lm (asn.treeAt t))
  have hlast := asn_countLE_last_zero asn
  have hpop_sum : ∑ i : Fin m, (if (asn.opsR i).isPop then 1 else 0) = popCount ops := by
    simp only [popCount, Finset.card_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [asn_isPop_eq asn i]
  omega

private theorem asn_total_countGE {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) :
    countGE asn.Rm (asn.treeAt 0) + ∑ i : Fin m, opInsGE asn.Rm (asn.opsR i) =
      ejectCount ops := by
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ)
    (fun i _ => asn_countGE_step asn i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have htel := sum_fin_telescope_nat (fun t => countGE asn.Rm (asn.treeAt t))
  have hlast := asn_countGE_last_zero asn
  have hej_sum : ∑ i : Fin m, (if (asn.opsR i).isEject then 1 else 0) = ejectCount ops := by
    simp only [ejectCount, Finset.card_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [asn_isEject_eq asn i]
  omega

/-- **Lemma 3.4** (`lem:spine-accounting`, Uncoupled Spine Potential Accounting):
Across `(init, ops)` under any `ThreeWayKeyAssignment`:
(1) `Rot(T_0, S) ≤ 2 C_POP(U) + 2 C_EJECT(W) + 9 (n + m)`;
(2) `EJECT` steps induce at most `max(0, 2 d_L - 2)` left single rotations on `U_t` (each along
`RS(U_t)`), and `POP` steps induce at most `max(0, 2 d_R - 2)` right single rotations on `W_t`
(each along `LS(W_t)`). -/
theorem lem_3_4_spine_accounting (h_3_1 : Ty_lem_3_1) (h_3_2 : Ty_lem_3_2)
    {α : Type} [LinearOrder α] (n m : ℕ)
    (init : BST α) (ops : Fin m → DequeOp α)
    (hn : init.tree.num_nodes = n) (hValid : ValidDequeSeq init.tree ops)
    (asn : ThreeWayKeyAssignment init ops) :
    -- Part (1)
    dequeSequenceCost init.tree ops ≤
      2 * (asn.cPopU : ℝ) + 2 * (asn.cEjectW : ℝ) + 9 * ((n : ℝ) + (m : ℝ)) ∧
    -- Part (2)
    asn.ejectInducedLeftRotsOnU ≤ 2 * popCount ops - 2 ∧
    asn.popInducedRightRotsOnW ≤ 2 * ejectCount ops - 2 ∧
    (∀ i : Fin m, (asn.opsR i).isEject →
      let pairs := (open Classical in
        (ejectCascadePairs (asn.treeAt i.castSucc)).filter
          (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL))
      (∀ p ∈ pairs, p.1 ∈ rightSpine (asn.U i.castSucc) ∧
        p.2 ∈ rightSpine (asn.U i.castSucc) ∧ p.2 < p.1) ∧
      asn.U i.succ = pairs.foldl (fun acc p => rotateLeftEdge acc p.1 p.2) (asn.U i.castSucc)) ∧
    (∀ i : Fin m, (asn.opsR i).isPop →
      let pairs := (open Classical in
        (popCascadePairs (asn.treeAt i.castSucc)).filter
          (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR))
      (∀ p ∈ pairs, p.1 ∈ leftSpine (asn.W i.castSucc) ∧
        p.2 ∈ leftSpine (asn.W i.castSucc) ∧ p.1 < p.2) ∧
      asn.W i.succ = pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (asn.W i.castSucc)) := by
  let _ := hValid
  classical
  -- Stepwise cascade rotation counts
  let cPopStep : Fin m → ℕ := fun i =>
    if (asn.opsR i).isPop then
      ((popCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)).length
    else 0
  let cEjStep : Fin m → ℕ := fun i =>
    if (asn.opsR i).isEject then
      ((ejectCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)).length
    else 0
  let ejOnUStep : Fin m → ℕ := fun i =>
    if (asn.opsR i).isEject then
      ((ejectCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)).length
    else 0
  let popOnWStep : Fin m → ℕ := fun i =>
    if (asn.opsR i).isPop then
      ((popCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)).length
    else 0
  -- Part (1): Amortized potential inequality at each step
  have hstep_cost : ∀ i : Fin m,
      (asn.opsR i).cost (asn.treeAt i.castSucc) +
        2 * (spinePot asn.Lm asn.Rm (asn.treeAt i.succ) : ℝ) -
        2 * (spinePot asn.Lm asn.Rm (asn.treeAt i.castSucc) : ℝ) ≤
      2 * (cPopStep i : ℝ) + 2 * (cEjStep i : ℝ) + 9 := by
    intro i
    have hstep_eq : asn.treeAt i.succ = (asn.opsR i).step (asn.treeAt i.castSucc) :=
      dequeSeq_step asn.T0 asn.opsR i
    have hbst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
    have hval : (asn.opsR i).Valid (asn.treeAt i.castSucc) := asn.hValidR i
    cases hop : asn.opsR i with
    | push q =>
      rw [hop] at hstep_eq
      have hpot := (push_pot_and_spines asn.hLmRm (asn.treeAt i.castSucc) q).1
      have hpot_r : (spinePot asn.Lm asn.Rm (SplayTree.push (asn.treeAt i.castSucc) q) : ℝ) ≤
          (spinePot asn.Lm asn.Rm (asn.treeAt i.castSucc) : ℝ) + 2 := by exact_mod_cast hpot
      simp only [cPopStep, cEjStep, hop, DequeOp.isPop, DequeOp.isEject,
        Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, DequeOp.cost, hstep_eq, DequeOp.step]
      linarith
    | inject q =>
      rw [hop] at hstep_eq
      have hpot := (inject_pot_and_spines asn.hLmRm (asn.treeAt i.castSucc) q).1
      have hpot_r : (spinePot asn.Lm asn.Rm (SplayTree.inject (asn.treeAt i.castSucc) q) : ℝ) ≤
          (spinePot asn.Lm asn.Rm (asn.treeAt i.castSucc) : ℝ) + 2 := by exact_mod_cast hpot
      simp only [cPopStep, cEjStep, hop, DequeOp.isPop, DequeOp.isEject,
        Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, DequeOp.cost, hstep_eq, DequeOp.step]
      linarith
    | pop =>
      rw [hop] at hstep_eq hval
      have hmin : ∀ xMin : ℝ, (asn.treeAt i.castSucc).minKey? = some xMin → xMin ≤ asn.Lm :=
        fun xMin hx => asn_pop_min_le_Lm asn i (by simp [hop, DequeOp.isPop]) xMin hx
      have hacc := (pop_step_accounting h_3_1 h_3_2 asn.hLmRm
        (asn.treeAt i.castSucc) hbst hval hmin).1
      have hpairs_eq :
          ((popCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)).length =
          ((popCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => decide (p.1 ≤ asn.Lm ∧ p.2 ≤ asn.Lm))).length :=
        congrArg List.length (asn_popPairs_VL_eq asn i.castSucc)
      simp only [cPopStep, cEjStep, hop, DequeOp.isPop, DequeOp.isEject,
        Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, DequeOp.cost, hstep_eq, DequeOp.step,
        hpairs_eq]
      linarith
    | eject =>
      rw [hop] at hstep_eq hval
      have hmax : ∀ zMax : ℝ, (asn.treeAt i.castSucc).maxKey? = some zMax → asn.Rm ≤ zMax :=
        fun zMax hz => asn_eject_max_ge_Rm asn i (by simp [hop, DequeOp.isEject]) zMax hz
      have hacc := (eject_step_accounting h_3_1 h_3_2 asn.hLmRm
        (asn.treeAt i.castSucc) hbst hval hmax).1
      have hpairs_eq :
          ((ejectCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)).length =
          ((ejectCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => decide (asn.Rm ≤ p.1 ∧ asn.Rm ≤ p.2))).length :=
        congrArg List.length (asn_ejPairs_VR_eq asn i.castSucc)
      simp only [cPopStep, cEjStep, hop, DequeOp.isPop, DequeOp.isEject,
        Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, DequeOp.cost, hstep_eq, DequeOp.step,
        hpairs_eq]
      linarith
  have hpart1 : dequeSequenceCost init.tree ops ≤
      2 * (asn.cPopU : ℝ) + 2 * (asn.cEjectW : ℝ) + 9 * ((n : ℝ) + (m : ℝ)) := by
    rw [← asn.hCost]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hstep_cost i)
    have hlhs : ∑ i : Fin m,
        ((asn.opsR i).cost (asn.treeAt i.castSucc) +
          2 * (spinePot asn.Lm asn.Rm (asn.treeAt i.succ) : ℝ) -
          2 * (spinePot asn.Lm asn.Rm (asn.treeAt i.castSucc) : ℝ)) =
        dequeSequenceCost asn.T0 asn.opsR +
          (2 * (spinePot asn.Lm asn.Rm (asn.treeAt (Fin.last m)) : ℝ) -
            2 * (spinePot asn.Lm asn.Rm asn.T0 : ℝ)) := by
      have htel := sum_fin_telescope_real
        (fun t => 2 * (spinePot asn.Lm asn.Rm (asn.treeAt t) : ℝ))
      have hcost_def : dequeSequenceCost asn.T0 asn.opsR =
          ∑ i : Fin m, (asn.opsR i).cost (asn.treeAt i.castSucc) := rfl
      have hsplit : ∑ i : Fin m,
          ((asn.opsR i).cost (asn.treeAt i.castSucc) +
            2 * (spinePot asn.Lm asn.Rm (asn.treeAt i.succ) : ℝ) -
            2 * (spinePot asn.Lm asn.Rm (asn.treeAt i.castSucc) : ℝ)) =
          (∑ i : Fin m, (asn.opsR i).cost (asn.treeAt i.castSucc)) +
          ∑ i : Fin m,
            (2 * (spinePot asn.Lm asn.Rm (asn.treeAt i.succ) : ℝ) -
              2 * (spinePot asn.Lm asn.Rm (asn.treeAt i.castSucc) : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      have h0_eq : asn.treeAt 0 = asn.T0 := rfl
      rw [hsplit, ← hcost_def]
      rw [h0_eq] at htel
      linarith
    have hrhs : ∑ i : Fin m, (2 * (cPopStep i : ℝ) + 2 * (cEjStep i : ℝ) + 9) =
        2 * (asn.cPopU : ℝ) + 2 * (asn.cEjectW : ℝ) + 9 * (m : ℝ) := by
      have hcPop_eq : (asn.cPopU : ℝ) = ∑ i : Fin m, (cPopStep i : ℝ) := by
        unfold ThreeWayKeyAssignment.cPopU
        push_cast
        refine Finset.sum_congr rfl (fun i _ => ?_)
        dsimp only [cPopStep]
        split_ifs <;> simp
      have hcEj_eq : (asn.cEjectW : ℝ) = ∑ i : Fin m, (cEjStep i : ℝ) := by
        unfold ThreeWayKeyAssignment.cEjectW
        push_cast
        refine Finset.sum_congr rfl (fun i _ => ?_)
        dsimp only [cEjStep]
        split_ifs <;> simp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hcPop_eq, hcEj_eq]
      simp [Finset.card_univ, Fintype.card_fin, mul_comm]
    have hpot0 : (spinePot asn.Lm asn.Rm asn.T0 : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast asn_init_pot_le h_3_1 hn asn
    have hpot_last : (0 : ℝ) ≤ (spinePot asn.Lm asn.Rm (asn.treeAt (Fin.last m)) : ℝ) :=
      Nat.cast_nonneg _
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  -- Part (2c) & (2d): Explicit structural action of EJECT on U_t and POP on W_t
  have hpart2_ej_struct : ∀ i : Fin m, (asn.opsR i).isEject →
      let pairs := (ejectCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)
      (∀ p ∈ pairs, p.1 ∈ rightSpine (asn.U i.castSucc) ∧
        p.2 ∈ rightSpine (asn.U i.castSucc) ∧ p.2 < p.1) ∧
      asn.U i.succ = pairs.foldl (fun acc p => rotateLeftEdge acc p.1 p.2) (asn.U i.castSucc) := by
    intro i hej
    have hstep_eq : asn.treeAt i.succ = (asn.opsR i).step (asn.treeAt i.castSucc) :=
      dequeSeq_step asn.T0 asn.opsR i
    have hbst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
    have hval : (asn.opsR i).Valid (asn.treeAt i.castSucc) := asn.hValidR i
    cases hop : asn.opsR i with
    | push _ => simp [hop, DequeOp.isEject] at hej
    | inject _ => simp [hop, DequeOp.isEject] at hej
    | pop => simp [hop, DequeOp.isEject] at hej
    | eject =>
      rw [hop] at hstep_eq hval
      have hmax : ∀ zMax : ℝ, (asn.treeAt i.castSucc).maxKey? = some zMax → asn.Rm ≤ zMax :=
        fun zMax hz => asn_eject_max_ge_Rm asn i hej zMax hz
      obtain ⟨_, _, _, _, h5, h6⟩ := eject_step_accounting h_3_1 h_3_2 asn.hLmRm
        (asn.treeAt i.castSucc) hbst hval hmax
      have hpairs_eq :
          (ejectCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL) =
          (ejectCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => decide (p.1 ≤ asn.Lm ∧ p.2 ≤ asn.Lm)) :=
        asn_ejPairs_VL_eq asn i.castSucc
      dsimp only
      rw [hpairs_eq]
      refine ⟨h5, ?_⟩
      unfold ThreeWayKeyAssignment.U
      rw [hstep_eq]
      exact h6
  have hpart2_pop_struct : ∀ i : Fin m, (asn.opsR i).isPop →
      let pairs := (popCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)
      (∀ p ∈ pairs, p.1 ∈ leftSpine (asn.W i.castSucc) ∧
        p.2 ∈ leftSpine (asn.W i.castSucc) ∧ p.1 < p.2) ∧
      asn.W i.succ = pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (asn.W i.castSucc) := by
    intro i hpop
    have hstep_eq : asn.treeAt i.succ = (asn.opsR i).step (asn.treeAt i.castSucc) :=
      dequeSeq_step asn.T0 asn.opsR i
    have hbst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
    have hval : (asn.opsR i).Valid (asn.treeAt i.castSucc) := asn.hValidR i
    cases hop : asn.opsR i with
    | push _ => simp [hop, DequeOp.isPop] at hpop
    | inject _ => simp [hop, DequeOp.isPop] at hpop
    | eject => simp [hop, DequeOp.isPop] at hpop
    | pop =>
      rw [hop] at hstep_eq hval
      have hmin : ∀ xMin : ℝ, (asn.treeAt i.castSucc).minKey? = some xMin → xMin ≤ asn.Lm :=
        fun xMin hx => asn_pop_min_le_Lm asn i hpop xMin hx
      obtain ⟨_, _, _, _, h5, h6⟩ := pop_step_accounting h_3_1 h_3_2 asn.hLmRm
        (asn.treeAt i.castSucc) hbst hval hmin
      have hpairs_eq :
          (popCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR) =
          (popCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => decide (asn.Rm ≤ p.1 ∧ asn.Rm ≤ p.2)) :=
        asn_popPairs_VR_eq asn i.castSucc
      dsimp only
      rw [hpairs_eq]
      refine ⟨h5, ?_⟩
      unfold ThreeWayKeyAssignment.W
      rw [hstep_eq]
      exact h6
  -- Stepwise |RS(U_t)| and |LS(W_t)| bounds for Part (2a) and (2b)
  have hrsU_step : ∀ i : Fin m,
      (rightSpine (asn.U i.succ)).length + ejOnUStep i ≤
        (rightSpine (asn.U i.castSucc)).length + opInsLE asn.Lm (asn.opsR i) +
          (if (asn.opsR i).isPop then 1 else 0) := by
    intro i
    have hstep_eq : asn.treeAt i.succ = (asn.opsR i).step (asn.treeAt i.castSucc) :=
      dequeSeq_step asn.T0 asn.opsR i
    have hbst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
    have hval : (asn.opsR i).Valid (asn.treeAt i.castSucc) := asn.hValidR i
    unfold ThreeWayKeyAssignment.U
    cases hop : asn.opsR i with
    | push q =>
      rw [hop] at hstep_eq
      have h := (push_pot_and_spines asn.hLmRm (asn.treeAt i.castSucc) q).2.1
      simp only [ejOnUStep, hop, DequeOp.isEject, DequeOp.isPop, Bool.false_eq_true,
        ↓reduceIte, opInsLE, hstep_eq, DequeOp.step]
      omega
    | inject q =>
      rw [hop] at hstep_eq
      have h := (inject_pot_and_spines asn.hLmRm (asn.treeAt i.castSucc) q).2.1
      simp only [ejOnUStep, hop, DequeOp.isEject, DequeOp.isPop, Bool.false_eq_true,
        ↓reduceIte, opInsLE, hstep_eq, DequeOp.step]
      omega
    | pop =>
      rw [hop] at hstep_eq hval
      have hmin : ∀ xMin : ℝ, (asn.treeAt i.castSucc).minKey? = some xMin → xMin ≤ asn.Lm :=
        fun xMin hx => asn_pop_min_le_Lm asn i (by simp [hop, DequeOp.isPop]) xMin hx
      have h := (pop_step_accounting h_3_1 h_3_2 asn.hLmRm
        (asn.treeAt i.castSucc) hbst hval hmin).2.2.1
      simp only [ejOnUStep, hop, DequeOp.isEject, DequeOp.isPop, Bool.false_eq_true,
        ↓reduceIte, opInsLE, hstep_eq, DequeOp.step]
      omega
    | eject =>
      rw [hop] at hstep_eq hval
      have hmax : ∀ zMax : ℝ, (asn.treeAt i.castSucc).maxKey? = some zMax → asn.Rm ≤ zMax :=
        fun zMax hz => asn_eject_max_ge_Rm asn i (by simp [hop, DequeOp.isEject]) zMax hz
      have h := (eject_step_accounting h_3_1 h_3_2 asn.hLmRm
        (asn.treeAt i.castSucc) hbst hval hmax).2.2.2.1
      have hpairs_eq :
          ((ejectCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)).length =
          ((ejectCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => decide (p.1 ≤ asn.Lm ∧ p.2 ≤ asn.Lm))).length :=
        congrArg List.length (asn_ejPairs_VL_eq asn i.castSucc)
      simp only [ejOnUStep, hop, DequeOp.isEject, DequeOp.isPop, Bool.false_eq_true,
        ↓reduceIte, opInsLE, hstep_eq, DequeOp.step, hpairs_eq]
      omega
  have hlsW_step : ∀ i : Fin m,
      (leftSpine (asn.W i.succ)).length + popOnWStep i ≤
        (leftSpine (asn.W i.castSucc)).length + opInsGE asn.Rm (asn.opsR i) +
          (if (asn.opsR i).isEject then 1 else 0) := by
    intro i
    have hstep_eq : asn.treeAt i.succ = (asn.opsR i).step (asn.treeAt i.castSucc) :=
      dequeSeq_step asn.T0 asn.opsR i
    have hbst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
    have hval : (asn.opsR i).Valid (asn.treeAt i.castSucc) := asn.hValidR i
    unfold ThreeWayKeyAssignment.W
    cases hop : asn.opsR i with
    | push q =>
      rw [hop] at hstep_eq
      have h := (push_pot_and_spines asn.hLmRm (asn.treeAt i.castSucc) q).2.2
      simp only [popOnWStep, hop, DequeOp.isPop, DequeOp.isEject, Bool.false_eq_true,
        ↓reduceIte, opInsGE, hstep_eq, DequeOp.step]
      omega
    | inject q =>
      rw [hop] at hstep_eq
      have h := (inject_pot_and_spines asn.hLmRm (asn.treeAt i.castSucc) q).2.2
      simp only [popOnWStep, hop, DequeOp.isPop, DequeOp.isEject, Bool.false_eq_true,
        ↓reduceIte, opInsGE, hstep_eq, DequeOp.step]
      omega
    | pop =>
      rw [hop] at hstep_eq hval
      have hmin : ∀ xMin : ℝ, (asn.treeAt i.castSucc).minKey? = some xMin → xMin ≤ asn.Lm :=
        fun xMin hx => asn_pop_min_le_Lm asn i (by simp [hop, DequeOp.isPop]) xMin hx
      have h := (pop_step_accounting h_3_1 h_3_2 asn.hLmRm
        (asn.treeAt i.castSucc) hbst hval hmin).2.2.2.1
      have hpairs_eq :
          ((popCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)).length =
          ((popCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => decide (asn.Rm ≤ p.1 ∧ asn.Rm ≤ p.2))).length :=
        congrArg List.length (asn_popPairs_VR_eq asn i.castSucc)
      simp only [popOnWStep, hop, DequeOp.isPop, DequeOp.isEject, Bool.false_eq_true,
        ↓reduceIte, opInsGE, hstep_eq, DequeOp.step, hpairs_eq]
      omega
    | eject =>
      rw [hop] at hstep_eq hval
      have hmax : ∀ zMax : ℝ, (asn.treeAt i.castSucc).maxKey? = some zMax → asn.Rm ≤ zMax :=
        fun zMax hz => asn_eject_max_ge_Rm asn i (by simp [hop, DequeOp.isEject]) zMax hz
      have h := (eject_step_accounting h_3_1 h_3_2 asn.hLmRm
        (asn.treeAt i.castSucc) hbst hval hmax).2.2.1
      simp only [popOnWStep, hop, DequeOp.isPop, DequeOp.isEject, Bool.false_eq_true,
        ↓reduceIte, opInsGE, hstep_eq, DequeOp.step]
      omega
  -- Part (2a): Bound asn.ejectInducedLeftRotsOnU ≤ 2 * popCount ops - 2
  have hejOnU_eq : asn.ejectInducedLeftRotsOnU = ∑ i : Fin m, ejOnUStep i := rfl
  have hrsU0_le : (rightSpine (asn.U 0)).length ≤ countLE asn.Lm (asn.treeAt 0) :=
    le_trans (rightSpine_length_le_num_nodes _)
      (restrictTree_Iic_nodes_le_countLE h_3_1 (asn.treeAt 0) asn.Lm (asn.hBST 0))
  have htotLE := asn_total_countLE asn
  have hpart2a : asn.ejectInducedLeftRotsOnU ≤ 2 * popCount ops - 2 := by
    rw [hejOnU_eq]
    let PopIdx : Finset (Fin m) := Finset.univ.filter (fun i => (asn.opsR i).isPop)
    have hPopIdx_card : PopIdx.card = popCount ops := by
      simp only [PopIdx, popCount]
      congr 1
      ext i
      simp [asn_isPop_eq asn i]
    by_cases hPop_empty : PopIdx = ∅
    · have hdL0 : popCount ops = 0 := by
        rw [← hPopIdx_card, hPop_empty, Finset.card_empty]
      have hpop_sum0 : ∑ i : Fin m, (if (asn.opsR i).isPop then 1 else 0) = 0 := by
        rw [← Finset.card_filter]
        change PopIdx.card = 0
        rw [hPopIdx_card, hdL0]
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrsU_step i)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        hpop_sum0] at hsum
      have htel := sum_fin_telescope_nat (fun t => (rightSpine (asn.U t)).length)
      omega
    · have hPop_ne : PopIdx.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPop_empty
      let iStar : Fin m := PopIdx.max' hPop_ne
      have hiStar_mem : iStar ∈ PopIdx := Finset.max'_mem PopIdx hPop_ne
      have hiStar_pop : (asn.opsR iStar).isPop = true := (Finset.mem_filter.mp hiStar_mem).2
      have hno_pop_after : ∀ j : Fin m, iStar.succ ≤ j.castSucc → (asn.opsR j).isPop = false := by
        intro j hle
        have hlt : iStar < j := Fin.lt_def.mpr (Fin.le_def.mp hle)
        by_contra htr
        simp only [Bool.not_eq_false] at htr
        have hj_in : j ∈ PopIdx := Finset.mem_filter.mpr ⟨Finset.mem_univ j, htr⟩
        exact not_lt_of_ge (Finset.le_max' PopIdx j hj_in) hlt
      have hmono : ∀ j : Fin m, iStar.succ ≤ j.castSucc →
          countLE asn.Lm (asn.treeAt j.castSucc) ≤ countLE asn.Lm (asn.treeAt j.succ) := by
        intro j hle
        have hstep_c := asn_countLE_step asn j
        have hnp := hno_pop_after j hle
        rw [hnp] at hstep_c
        simp only [Bool.false_eq_true, ↓reduceIte] at hstep_c
        omega
      have hc_zero_after : countLE asn.Lm (asn.treeAt iStar.succ) = 0 := by
        have hle := fin_mono_from (fun t => countLE asn.Lm (asn.treeAt t)) iStar.succ hmono
          (Fin.last m) (Fin.le_last _)
        have hlast := asn_countLE_last_zero asn
        omega
      have hU_succ_nil : asn.U iStar.succ = .nil :=
        restrictTree_Iic_eq_nil_of_countLE_zero _ _ hc_zero_after
      have hU_cs_ne : asn.U iStar.castSucc ≠ .nil := by
        have hbst : (asn.treeAt iStar.castSucc).IsBST := asn.hBST iStar.castSucc
        have hval : (asn.opsR iStar).Valid (asn.treeAt iStar.castSucc) := asn.hValidR iStar
        cases hop : asn.opsR iStar with
        | push _ => simp [hop, DequeOp.isPop] at hiStar_pop
        | inject _ => simp [hop, DequeOp.isPop] at hiStar_pop
        | eject => simp [hop, DequeOp.isPop] at hiStar_pop
        | pop =>
          rw [hop] at hval
          have hmin : ∀ xMin : ℝ, (asn.treeAt iStar.castSucc).minKey? = some xMin → xMin ≤ asn.Lm :=
            fun xMin hx => asn_pop_min_le_Lm asn iStar hiStar_pop xMin hx
          exact (pop_step_accounting h_3_1 h_3_2 asn.hLmRm
            (asn.treeAt iStar.castSucc) hbst hval hmin).2.1
      have hrs_cs_pos : 1 ≤ (rightSpine (asn.U iStar.castSucc)).length := by
        have hne_list : rightSpine (asn.U iStar.castSucc) ≠ [] :=
          mt (rightSpine_eq_nil_iff _).mp hU_cs_ne
        exact Nat.succ_le_of_lt (List.length_pos_iff_ne_nil.mpr hne_list)
      have hrs_succ_zero : (rightSpine (asn.U iStar.succ)).length = 0 := by
        simp [hU_succ_nil, rightSpine]
      have hstar_step :
          (rightSpine (asn.U iStar.succ)).length + ejOnUStep iStar + 1 ≤
            (rightSpine (asn.U iStar.castSucc)).length + opInsLE asn.Lm (asn.opsR iStar) := by
        have h0 : ejOnUStep iStar = 0 := by
          cases hop : asn.opsR iStar <;>
            simp [ejOnUStep, hop, DequeOp.isPop, DequeOp.isEject] at hiStar_pop ⊢
        omega
      -- Strengthened stepwise bound adding +1 on left at iStar and dropping +1 on right at iStar
      have hrsU_step' : ∀ i : Fin m,
          (rightSpine (asn.U i.succ)).length + ejOnUStep i + (if i = iStar then 1 else 0) ≤
            (rightSpine (asn.U i.castSucc)).length + opInsLE asn.Lm (asn.opsR i) +
              (if (asn.opsR i).isPop ∧ i ≠ iStar then 1 else 0) := by
        intro i
        by_cases hi : i = iStar
        · subst hi
          simp only [↓reduceIte, ne_eq, not_true_eq_false, and_false]
          omega
        · have h := hrsU_step i
          simp only [hi, ↓reduceIte, ne_eq, not_false_eq_true, and_true]
          exact h
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrsU_step' i)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
      have hsum_iStar : ∑ i : Fin m, (if i = iStar then 1 else 0) = 1 := by
        simp [Finset.mem_univ]
      have hsum_pop_minus :
          ∑ i : Fin m, (if (asn.opsR i).isPop ∧ i ≠ iStar then 1 else 0) + 1 = popCount ops := by
        have hfilt_eq : Finset.univ.filter (fun i : Fin m => (asn.opsR i).isPop ∧ i ≠ iStar) =
            PopIdx.erase iStar := by
          ext i; simp [PopIdx, and_comm]
        rw [← Finset.card_filter, hfilt_eq, Finset.card_erase_add_one hiStar_mem, hPopIdx_card]
      have htel := sum_fin_telescope_nat (fun t => (rightSpine (asn.U t)).length)
      omega
  -- Part (2b): Symmetric bound asn.popInducedRightRotsOnW ≤ 2 * ejectCount ops - 2
  have hpopOnW_eq : asn.popInducedRightRotsOnW = ∑ i : Fin m, popOnWStep i := rfl
  have hlsW0_le : (leftSpine (asn.W 0)).length ≤ countGE asn.Rm (asn.treeAt 0) :=
    le_trans (leftSpine_length_le_num_nodes _)
      (restrictTree_Ici_nodes_le_countGE h_3_1 (asn.treeAt 0) asn.Rm (asn.hBST 0))
  have htotGE := asn_total_countGE asn
  have hpart2b : asn.popInducedRightRotsOnW ≤ 2 * ejectCount ops - 2 := by
    rw [hpopOnW_eq]
    let EjIdx : Finset (Fin m) := Finset.univ.filter (fun i => (asn.opsR i).isEject)
    have hEjIdx_card : EjIdx.card = ejectCount ops := by
      simp only [EjIdx, ejectCount]
      congr 1
      ext i
      simp [asn_isEject_eq asn i]
    by_cases hEj_empty : EjIdx = ∅
    · have hdR0 : ejectCount ops = 0 := by
        rw [← hEjIdx_card, hEj_empty, Finset.card_empty]
      have hej_sum0 : ∑ i : Fin m, (if (asn.opsR i).isEject then 1 else 0) = 0 := by
        rw [← Finset.card_filter]
        change EjIdx.card = 0
        rw [hEjIdx_card, hdR0]
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlsW_step i)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        hej_sum0] at hsum
      have htel := sum_fin_telescope_nat (fun t => (leftSpine (asn.W t)).length)
      omega
    · have hEj_ne : EjIdx.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEj_empty
      let jStar : Fin m := EjIdx.max' hEj_ne
      have hjStar_mem : jStar ∈ EjIdx := Finset.max'_mem EjIdx hEj_ne
      have hjStar_ej : (asn.opsR jStar).isEject = true := (Finset.mem_filter.mp hjStar_mem).2
      have hno_ej_after : ∀ j : Fin m, jStar.succ ≤ j.castSucc → (asn.opsR j).isEject = false := by
        intro j hle
        have hlt : jStar < j := Fin.lt_def.mpr (Fin.le_def.mp hle)
        by_contra htr
        simp only [Bool.not_eq_false] at htr
        have hj_in : j ∈ EjIdx := Finset.mem_filter.mpr ⟨Finset.mem_univ j, htr⟩
        exact not_lt_of_ge (Finset.le_max' EjIdx j hj_in) hlt
      have hmono : ∀ j : Fin m, jStar.succ ≤ j.castSucc →
          countGE asn.Rm (asn.treeAt j.castSucc) ≤ countGE asn.Rm (asn.treeAt j.succ) := by
        intro j hle
        have hstep_c := asn_countGE_step asn j
        have hne_ej := hno_ej_after j hle
        rw [hne_ej] at hstep_c
        simp only [Bool.false_eq_true, ↓reduceIte] at hstep_c
        omega
      have hc_zero_after : countGE asn.Rm (asn.treeAt jStar.succ) = 0 := by
        have hle := fin_mono_from (fun t => countGE asn.Rm (asn.treeAt t)) jStar.succ hmono
          (Fin.last m) (Fin.le_last _)
        have hlast := asn_countGE_last_zero asn
        omega
      have hW_succ_nil : asn.W jStar.succ = .nil :=
        restrictTree_Ici_eq_nil_of_countGE_zero _ _ hc_zero_after
      have hW_cs_ne : asn.W jStar.castSucc ≠ .nil := by
        have hbst : (asn.treeAt jStar.castSucc).IsBST := asn.hBST jStar.castSucc
        have hval : (asn.opsR jStar).Valid (asn.treeAt jStar.castSucc) := asn.hValidR jStar
        cases hop : asn.opsR jStar with
        | push _ => simp [hop, DequeOp.isEject] at hjStar_ej
        | inject _ => simp [hop, DequeOp.isEject] at hjStar_ej
        | pop => simp [hop, DequeOp.isEject] at hjStar_ej
        | eject =>
          rw [hop] at hval
          have hmax : ∀ zMax : ℝ, (asn.treeAt jStar.castSucc).maxKey? = some zMax → asn.Rm ≤ zMax :=
            fun zMax hz => asn_eject_max_ge_Rm asn jStar hjStar_ej zMax hz
          exact (eject_step_accounting h_3_1 h_3_2 asn.hLmRm
            (asn.treeAt jStar.castSucc) hbst hval hmax).2.1
      have hls_cs_pos : 1 ≤ (leftSpine (asn.W jStar.castSucc)).length := by
        have hne_list : leftSpine (asn.W jStar.castSucc) ≠ [] :=
          mt (leftSpine_eq_nil_iff _).mp hW_cs_ne
        exact Nat.succ_le_of_lt (List.length_pos_iff_ne_nil.mpr hne_list)
      have hls_succ_zero : (leftSpine (asn.W jStar.succ)).length = 0 := by
        simp [hW_succ_nil, leftSpine]
      have hstar_step :
          (leftSpine (asn.W jStar.succ)).length + popOnWStep jStar + 1 ≤
            (leftSpine (asn.W jStar.castSucc)).length + opInsGE asn.Rm (asn.opsR jStar) := by
        have h0 : popOnWStep jStar = 0 := by
          cases hop : asn.opsR jStar <;>
            simp [popOnWStep, hop, DequeOp.isPop, DequeOp.isEject] at hjStar_ej ⊢
        omega
      have hlsW_step' : ∀ i : Fin m,
          (leftSpine (asn.W i.succ)).length + popOnWStep i + (if i = jStar then 1 else 0) ≤
            (leftSpine (asn.W i.castSucc)).length + opInsGE asn.Rm (asn.opsR i) +
              (if (asn.opsR i).isEject ∧ i ≠ jStar then 1 else 0) := by
        intro i
        by_cases hi : i = jStar
        · subst hi
          simp only [↓reduceIte, ne_eq, not_true_eq_false, and_false]
          omega
        · have h := hlsW_step i
          simp only [hi, ↓reduceIte, ne_eq, not_false_eq_true, and_true]
          exact h
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlsW_step' i)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
      have hsum_jStar : ∑ i : Fin m, (if i = jStar then 1 else 0) = 1 := by
        simp [Finset.mem_univ]
      have hsum_ej_minus :
          ∑ i : Fin m, (if (asn.opsR i).isEject ∧ i ≠ jStar then 1 else 0) + 1 = ejectCount ops := by
        have hfilt_eq : Finset.univ.filter (fun i : Fin m => (asn.opsR i).isEject ∧ i ≠ jStar) =
            EjIdx.erase jStar := by
          ext i; simp [EjIdx, and_comm]
        rw [← Finset.card_filter, hfilt_eq, Finset.card_erase_add_one hjStar_mem, hEjIdx_card]
      have htel := sum_fin_telescope_nat (fun t => (leftSpine (asn.W t)).length)
      omega
  exact ⟨hpart1, hpart2a, hpart2b, hpart2_ej_struct, hpart2_pop_struct⟩

end Solution.KeyAssignmentSpine
